//  Copyright 2024, University of Freiburg,
//                  Chair of Algorithms and Data Structures
//  Author: Hannes Baumann <baumannh@informatik.uni-freiburg.de>

#include "engine/sparqlExpressions/PrefilterExpressionIndex.h"

#include <ranges>

#include "global/ValueIdComparators.h"
#include "util/ConstexprMap.h"
#include "util/OverloadCallOperator.h"

namespace prefilterExpressions {

// HELPER FUNCTIONS
//______________________________________________________________________________
// Given a PermutedTriple retrieve the suitable Id w.r.t. a column (index).
static Id getIdFromColumnIndex(const BlockMetadata::PermutedTriple& triple,
                               size_t columnIndex) {
  switch (columnIndex) {
    case 0:
      return triple.col0Id_;
    case 1:
      return triple.col1Id_;
    case 2:
      return triple.col2Id_;
    default:
      // columnIndex out of bounds
      AD_FAIL();
  }
};

//______________________________________________________________________________
// Extract the Ids from the given `PermutedTriple` in a tuple w.r.t. the
// position (column index) defined by `ignoreIndex`. The ignored positions are
// filled with Ids `Id::min()`. `Id::min()` is guaranteed
// to be smaller than Ids of all other types.
static auto getMaskedTriple(const BlockMetadata::PermutedTriple& triple,
                            size_t ignoreIndex = 3) {
  const Id& undefined = Id::min();
  switch (ignoreIndex) {
    case 3:
      return std::make_tuple(triple.col0Id_, triple.col1Id_, triple.col2Id_);
    case 2:
      return std::make_tuple(triple.col0Id_, triple.col1Id_, undefined);
    case 1:
      return std::make_tuple(triple.col0Id_, undefined, undefined);
    case 0:
      return std::make_tuple(undefined, undefined, undefined);
    default:
      // ignoreIndex out of bounds
      AD_FAIL();
  }
};

//______________________________________________________________________________
// Check for constant values in all columns `< evaluationColumn`
static bool checkBlockIsInconsistent(const BlockMetadata& block,
                                     size_t evaluationColumn) {
  return getMaskedTriple(block.firstTriple_, evaluationColumn) !=
         getMaskedTriple(block.lastTriple_, evaluationColumn);
}

//______________________________________________________________________________
// Check required conditions.
static void checkEvalRequirements(std::span<const BlockMetadata> input,
                                  size_t evaluationColumn) {
  const auto throwRuntimeError = [](const std::string& errorMessage) {
    throw std::runtime_error(errorMessage);
  };
  // Check for duplicates.
  if (auto it = ql::ranges::adjacent_find(input); it != input.end()) {
    throwRuntimeError("The provided data blocks must be unique.");
  }
  // Helper to check for fully sorted blocks. Return `true` if `b1 < b2` is
  // satisfied.
  const auto checkOrder = [](const BlockMetadata& b1, const BlockMetadata& b2) {
    if (b1.blockIndex_ < b2.blockIndex_) {
      AD_CORRECTNESS_CHECK(getMaskedTriple(b1.lastTriple_) <=
                           getMaskedTriple(b2.lastTriple_));
      return true;
    }
    if (b1.blockIndex_ == b2.blockIndex_) {
      // Given the previous check detects duplicates in the input, the
      // correctness check here will never evaluate to true.
      // => blockIndex_ assignment issue.
      AD_CORRECTNESS_CHECK(b1 == b2);
    } else {
      AD_CORRECTNESS_CHECK(getMaskedTriple(b1.lastTriple_) >
                           getMaskedTriple(b2.firstTriple_));
    }
    return false;
  };
  if (!ql::ranges::is_sorted(input, checkOrder)) {
    throwRuntimeError("The blocks must be provided in sorted order.");
  }
  // Helper to check for column consistency. Returns `true` if the columns for
  // `b1` and `b2` up to the evaluation are inconsistent.
  const auto checkColumnConsistency =
      [evaluationColumn](const BlockMetadata& b1, const BlockMetadata& b2) {
        return checkBlockIsInconsistent(b1, evaluationColumn) ||
               getMaskedTriple(b1.lastTriple_, evaluationColumn) !=
                   getMaskedTriple(b2.firstTriple_, evaluationColumn) ||
               checkBlockIsInconsistent(b2, evaluationColumn);
      };
  if (auto it = ql::ranges::adjacent_find(input, checkColumnConsistency);
      it != input.end()) {
    throwRuntimeError(
        "The values in the columns up to the evaluation column must be "
        "consistent.");
  }
};

//______________________________________________________________________________
// Given the arguments `std::span<const BlockMetadata> input` and
// `evaluationColumn`, this function retrieves the `Id`s of column index
// `evaluationColumn` from BlockMetadata and the `BlockMetadata`
// values containing mixed datatypes.
static std::pair<std::vector<ValueId>, std::vector<BlockMetadata>>
getValueIdsAndMixedDatatypeBlocks(std::span<const BlockMetadata> input,
                                  size_t evaluationColumn) {
  std::vector<ValueId> idVector;
  // For each BlockMetadata value in vector input, we have a respective Id for
  // firstTriple and lastTriple
  idVector.reserve(2 * input.size());
  std::vector<BlockMetadata> mixedDatatypeBlocks;

  ql::ranges::for_each(input, [&](const BlockMetadata& block) {
    const auto firstId =
        getIdFromColumnIndex(block.firstTriple_, evaluationColumn);
    const auto secondId =
        getIdFromColumnIndex(block.lastTriple_, evaluationColumn);

    idVector.push_back(firstId);
    idVector.push_back(secondId);

    if (firstId.getDatatype() != secondId.getDatatype()) {
      mixedDatatypeBlocks.push_back(block);
    }
  });
  return {idVector, mixedDatatypeBlocks};
}

//______________________________________________________________________________
static std::vector<BlockMetadata> getRelevantBlocks(
    RelevantBlockRanges relevantBlockRanges,
    std::span<const BlockMetadata> blocks) {
  std::vector<BlockMetadata> relevantBlocks;
  for (const auto& [rangeBegin, rangeEnd] : relevantBlockRanges) {
    assert(rangeBegin > 0 && rangeEnd < blocks.size());
    relevantBlocks.insert(relevantBlocks.end(), blocks.begin() + rangeBegin,
                          blocks.begin() + rangeEnd);
  }
  return relevantBlocks;
}

//______________________________________________________________________________
static RelevantBlockRanges getUnion(RelevantBlockRanges r1,
                                    RelevantBlockRanges r2) {
  // (1) If r1 is empty, the union of r2 with r1 is simply r2.
  // (2) If r2 is empty, the union of r1 with r2 is simply r1.
  // (3) Given both are empty, the empty vector is automatically
  // returned here with (1) and (2).
  if (r1.empty()) return r2;
  if (r2.empty()) return r1;

  RelevantBlockRanges unionedRanges;
  unionedRanges.reserve(r1.size() + r2.size());
  auto idx1 = r1.begin(), idx2 = r2.begin();
  size_t lastMaxIdx = 0;

  while (idx1 != r1.end() && idx2 != r2.end()) {
    const auto& [idx1First, idx1Second] = *idx1;
    const auto& [idx2First, idx2Second] = *idx2;
    if (idx1Second < lastMaxIdx) {
      idx1++;
    } else if (idx2Second < lastMaxIdx) {
      idx2++;
    } else if (idx2Second < idx1First) {
      // Handle no overlap.
      // BlockRange of r2 < BlockRange of r1 overall.
      unionedRanges.emplace_back(std::max(idx2First, lastMaxIdx), idx2Second);
      lastMaxIdx = idx2Second;
      // Skip to the next range in `r2`.
      idx2++;
    } else if (idx1Second < idx2First) {
      // Handle no overlap.
      // BlockRange of r1 < BlockRange of r2 overall.
      unionedRanges.emplace_back(std::max(idx1First, lastMaxIdx), idx1Second);
      lastMaxIdx = idx1Second;
      // Skip to the next range in `r1`.
      idx1++;
    } else {
      // Handle overlapping ranges.
      // Avoid adding indices twice by setting lastMaxIdx to the highest index
      // value added so far.
      // See above: If-branches with `idx1Second < lastMaxIdx` or `idx2Second <
      // lastMaxId` + potential skipping avoids adding indices twice.
      auto newlastMaxIdx = std::max(idx1Second, idx2Second);
      assert(newlastMaxIdx > lastMaxIdx);
      unionedRanges.emplace_back(
          std::max(std::min(idx1First, idx2First), lastMaxIdx), newlastMaxIdx);
      lastMaxIdx = newlastMaxIdx;
      // Skip to the next range for `r1` and `r2`.
      idx1++, idx2++;
    }
  }

  const auto optAddAdjustedRange = [&unionedRanges,
                                    &lastMaxIdx](const BlockRange& range) {
    if (range.first >= lastMaxIdx) {
      unionedRanges.emplace_back(std::max(range.first, lastMaxIdx),
                                 range.second);
    }
  };
  // Add the additional `BlockRange`s of r1 or r2 to unionedRanges.
  ql::ranges::for_each(idx1, r1.end(), optAddAdjustedRange);
  ql::ranges::for_each(idx2, r2.end(), optAddAdjustedRange);
  return unionedRanges;
}

//______________________________________________________________________________
static RelevantBlockRanges getIntersection(RelevantBlockRanges r1,
                                           RelevantBlockRanges r2) {
  // If one of the ranges is empty, the intersection by definition is empty.
  if (r1.empty() || r2.empty()) return {};

  RelevantBlockRanges intersectedRanges;
  intersectedRanges.reserve(r1.size() + r2.size());
  auto idx1 = r1.begin(), idx2 = r2.begin();

  while (idx1 != r1.end() && idx2 != r2.end()) {
    const auto& [idx1First, idx1Second] = *idx1;
    const auto& [idx2First, idx2Second] = *idx2;
    // Handle no overlap w.r.t. current ranges, the intersection is empty.
    if (idx1Second < idx2First) {
      idx1++;
      continue;
    }
    if (idx2Second < idx1First) {
      idx2++;
      continue;
    }
    // The ranges overlap, retrieve the intersection.
    intersectedRanges.emplace_back(std::max(idx1First, idx2First),
                                   std::min(idx1Second, idx2Second));
    if (idx1Second < idx2Second) {
      idx1++;
    } else if (idx2Second < idx1Second) {
      idx2++;
    } else {
      // If idx2Second is equal to idx1Second, skip for both to the next
      // respective range.
      idx1++, idx2++;
    }
  }
  // The remaining BlockRange values from r1 or r2 are simply discarded given we
  // completely iterated over r1 and/or r2. No additional intersections are
  // possible.
  return intersectedRanges;
}

//______________________________________________________________________________
// Refers to an `ValueId` span `::iterator` (index).
using RandomIt = std::span<const ValueId>::iterator;
// A pair containing the `start` and `end` (iterator) indices for a specified
// single datatype range over a given `const ValueId` span.
// For the given cases below, the `ValueId` span is retrieved from the
// `BlockMetadata` values. And those `ValueId` values define the bounds of the
// related `BlockMetadata` values.
using RandomItPair = std::pair<RandomIt, RandomIt>;

//______________________________________________________________________________
// Helper for adding the relevant ranges to `blockRangeIndices`.
// `addRangeAndSimplify` ensures that the ranges added are non-overlapping and
// merged together if adjacent.
const auto addRangeAndSimplify = [](RelevantBlockRanges& blockRangeIndices,
                                    const size_t rangeIdxFirst,
                                    const size_t rangeIdxSecond) {
  // Simplify the mapped ranges if adjacent or overlapping.
  // This simplification procedure also ensures that no `BlockMetadata`
  // value is retrieved twice later on (no overlapping indices for adjacient
  // `BlockRange` values).
  if (!blockRangeIndices.empty() &&
      blockRangeIndices.back().second >= rangeIdxFirst) {
    // They are adjacent or even overlap: merge/simplify!
    blockRangeIndices.back().second = rangeIdxSecond;
  } else {
    // The new range (specified by `BlockRange`) is not adjacent and
    // doesn't overlap.
    blockRangeIndices.emplace_back(rangeIdxFirst, rangeIdxSecond);
  }
};

//______________________________________________________________________________
static RelevantBlockRanges mapRandomItRangesToBlockRangesComplemented(
    const std::vector<RandomItPair>& relevantIdRanges,
    std::span<const ValueId> idVec) {
  auto idVecBegin = idVec.begin();
  auto idVecEnd = idVec.end();
  // Vector containing the `BlockRange` mapped indices.
  RelevantBlockRanges blockRanges;
  blockRanges.reserve(relevantIdRanges.size());
  // Helper to properly add the range defining index pair to `blockRanges`. This
  // procedure ensures that the added ranges dont't overlap by merging them if
  // required.
  const auto addRange = [&blockRanges](const size_t rangeIdxFirst,
                                       const size_t rangeIdxSecond) {
    addRangeAndSimplify(blockRanges, rangeIdxFirst, rangeIdxSecond);
  };

  // The MAX index (allowed difference).
  const auto maxIndex = std::distance(idVecBegin, idVecEnd);
  RandomIt lastIdRangeIt = idVecBegin;

  for (const auto& [firstIdRangeIt, secondIdRangeIt] : relevantIdRanges) {
    addRange(
        static_cast<size_t>(std::distance(idVecBegin, lastIdRangeIt) / 2),
        // Ensure that we respect the bounds of the `BlockMetadata` value
        // vector later on.
        static_cast<size_t>(std::min(
            (std::distance(idVecBegin, firstIdRangeIt) + 1) / 2, maxIndex)));
    // Set the start of the next complementing section.
    lastIdRangeIt = secondIdRangeIt;
  }
  // Handle the last complementing section.
  const auto& mappedBlockRangeFirst = std::distance(idVecBegin, lastIdRangeIt);
  if (mappedBlockRangeFirst < maxIndex) {
    addRange(static_cast<size_t>(mappedBlockRangeFirst / 2),
             static_cast<size_t>(maxIndex));
  }
  return blockRanges;
}

//______________________________________________________________________________
static RelevantBlockRanges mapRandomItRangesToBlockRanges(
    const std::vector<RandomItPair>& relevantIdRanges,
    std::span<const ValueId> idVec) {
  auto idVecBegin = idVec.begin();
  auto idVecEnd = idVec.end();
  // Vector containing the `BlockRange` mapped indices.
  RelevantBlockRanges blockRanges;
  blockRanges.reserve(relevantIdRanges.size());
  // Helper to properly add the range defining index pair to `blockRanges`. This
  // procedure ensures that the added ranges dont't overlap by merging them if
  // required.
  const auto addRange = [&blockRanges](const size_t rangeIdxFirst,
                                       const size_t rangeIdxSecond) {
    addRangeAndSimplify(blockRanges, rangeIdxFirst, rangeIdxSecond);
  };

  // The MAX index (allowed difference).
  const auto maxIndex = std::distance(idVecBegin, idVecEnd);

  for (const auto& [firstIdRangeIt, secondIdRangeIt] : relevantIdRanges) {
    assert(firstIdRangeIt <= secondIdRangeIt);
    addRange(
        static_cast<size_t>(std::distance(idVecBegin, firstIdRangeIt) / 2),
        // Ensure that we respect the bounds of the `BlockMetadata` value vector
        // later on.
        static_cast<size_t>(std::min(
            (std::distance(idVecBegin, secondIdRangeIt) + 1) / 2, maxIndex)));
  }
  return blockRanges;
}

//______________________________________________________________________________
// Given two sorted `vector`s containing `BlockMetadata`, this function
// returns their merged `BlockMetadata` content in a `vector` which is free of
// duplicates and ordered.
static auto getSetUnion(const std::vector<BlockMetadata>& blocks1,
                        const std::vector<BlockMetadata>& blocks2) {
  std::vector<BlockMetadata> mergedVectors;
  mergedVectors.reserve(blocks1.size() + blocks2.size());
  const auto blockLessThanBlock = [](const BlockMetadata& b1,
                                     const BlockMetadata& b2) {
    return b1.blockIndex_ < b2.blockIndex_;
  };
  // Given that we have vectors with sorted (BlockMedata) values, we can
  // use ql::ranges::set_union. Thus the complexity is O(n + m).
  ql::ranges::set_union(blocks1, blocks2, std::back_inserter(mergedVectors),
                        blockLessThanBlock);
  mergedVectors.shrink_to_fit();
  return mergedVectors;
}

//______________________________________________________________________________
// Return `CompOp`s as string.
static std::string getRelationalOpStr(const CompOp relOp) {
  using enum CompOp;
  switch (relOp) {
    case LT:
      return "LT(<)";
    case LE:
      return "LE(<=)";
    case EQ:
      return "EQ(=)";
    case NE:
      return "NE(!=)";
    case GE:
      return "GE(>=)";
    case GT:
      return "GT(>)";
    default:
      AD_FAIL();
  }
}

//______________________________________________________________________________
// Return `LogicalOperator`s as string.
static std::string getLogicalOpStr(const LogicalOperator logOp) {
  using enum LogicalOperator;
  switch (logOp) {
    case AND:
      return "AND(&&)";
    case OR:
      return "OR(||)";
    default:
      AD_FAIL();
  }
}

// SECTION PREFILTER EXPRESSION (BASE CLASS)
//______________________________________________________________________________
std::vector<BlockMetadata> PrefilterExpression::evaluate(
    std::span<const BlockMetadata> input, size_t evaluationColumn) const {
  if (input.size() < 3) {
    return std::vector<BlockMetadata>(input.begin(), input.end());
  }

  std::optional<BlockMetadata> firstBlock = std::nullopt;
  std::optional<BlockMetadata> lastBlock = std::nullopt;
  if (checkBlockIsInconsistent(input.front(), evaluationColumn)) {
    firstBlock = input.front();
    input = input.subspan(1);
  }
  if (checkBlockIsInconsistent(input.back(), evaluationColumn)) {
    lastBlock = input.back();
    input = input.subspan(0, input.size() - 1);
  }

  checkEvalRequirements(input, evaluationColumn);
  const auto [idVector, mixedDatatypeBlocks] =
      getValueIdsAndMixedDatatypeBlocks(input, evaluationColumn);
  auto result = getRelevantBlocks(evaluateImpl(idVector), input);
  checkEvalRequirements(result, evaluationColumn);

  if (firstBlock.has_value()) {
    result.insert(result.begin(), firstBlock.value());
  }
  if (lastBlock.has_value()) {
    result.push_back(lastBlock.value());
  }
  return getSetUnion(result, mixedDatatypeBlocks);
};

//______________________________________________________________________________
ValueId PrefilterExpression::getValueIdFromIdOrLocalVocabEntry(
    const IdOrLocalVocabEntry& referenceValue, LocalVocab& vocab) {
  return std::visit(ad_utility::OverloadCallOperator{
                        [](const ValueId& referenceId) { return referenceId; },
                        [&vocab](const LocalVocabEntry& referenceLVE) {
                          return Id::makeFromLocalVocabIndex(
                              vocab.getIndexAndAddIfNotContained(referenceLVE));
                        }},
                    referenceValue);
}

// SECTION RELATIONAL OPERATIONS
//______________________________________________________________________________
template <CompOp Comparison>
std::unique_ptr<PrefilterExpression>
RelationalExpression<Comparison>::logicalComplement() const {
  using enum CompOp;
  using namespace ad_utility;
  using P = std::pair<CompOp, CompOp>;
  // The complementation logic implemented with the following mapping procedure:
  // (1) ?var < referenceValue -> ?var >= referenceValue
  // (2) ?var <= referenceValue -> ?var > referenceValue
  // (3) ?var >= referenceValue -> ?var < referenceValue
  // (4) ?var > referenceValue -> ?var <= referenceValue
  // (5) ?var = referenceValue -> ?var != referenceValue
  // (6) ?var != referenceValue -> ?var = referenceValue
  constexpr ConstexprMap<CompOp, CompOp, 6> complementMap(
      {P{LT, GE}, P{LE, GT}, P{GE, LT}, P{GT, LE}, P{EQ, NE}, P{NE, EQ}});
  return std::make_unique<RelationalExpression<complementMap.at(Comparison)>>(
      rightSideReferenceValue_);
};

//______________________________________________________________________________
template <CompOp Comparison>
RelevantBlockRanges RelationalExpression<Comparison>::evaluateImpl(
    std::span<const ValueId> idSpan) const {
  using namespace valueIdComparators;
  auto beginIdSpan = idSpan.begin();
  auto endIdSpan = idSpan.end();
  // If `rightSideReferenceValue_` contains a `LocalVocabEntry` value, we use
  // the here created `LocalVocab` to retrieve a corresponding `ValueId`.
  LocalVocab vocab{};
  auto referenceId =
      getValueIdFromIdOrLocalVocabEntry(rightSideReferenceValue_, vocab);
  // Use getRangesForId (from valueIdComparators) to extract the ranges
  // containing the relevant ValueIds.
  // For pre-filtering with CompOp::EQ, we have to consider empty ranges.
  // Reason: The referenceId could be contained within the bounds formed by
  // the IDs of firstTriple_ and lastTriple_ (set false flag to keep
  // empty ranges).
  auto relevantIdRanges =
      Comparison != CompOp::EQ
          ? getRangesForId(beginIdSpan, endIdSpan, referenceId, Comparison)
          : getRangesForId(beginIdSpan, endIdSpan, referenceId, Comparison,
                           false);
  valueIdComparators::detail::simplifyRanges(relevantIdRanges);
  // Map the relevant range w.r.t. the flat `std::span<const ValueId>` to ranges
  // w.r.t. `std::span<const Block>` represented by index pairs
  // (`std::pair<size_t, size_t>`).
  return mapRandomItRangesToBlockRanges(relevantIdRanges, idSpan);
};

//______________________________________________________________________________
template <CompOp Comparison>
bool RelationalExpression<Comparison>::operator==(
    const PrefilterExpression& other) const {
  const auto* otherRelational =
      dynamic_cast<const RelationalExpression<Comparison>*>(&other);
  if (!otherRelational) {
    return false;
  }
  return rightSideReferenceValue_ == otherRelational->rightSideReferenceValue_;
};

//______________________________________________________________________________
template <CompOp Comparison>
std::unique_ptr<PrefilterExpression> RelationalExpression<Comparison>::clone()
    const {
  return std::make_unique<RelationalExpression<Comparison>>(
      rightSideReferenceValue_);
};

//______________________________________________________________________________
template <CompOp Comparison>
std::string RelationalExpression<Comparison>::asString(
    [[maybe_unused]] size_t depth) const {
  auto referenceValueToString = [](std::stringstream& stream,
                                   const IdOrLocalVocabEntry& referenceValue) {
    std::visit(
        ad_utility::OverloadCallOperator{
            [&stream](const ValueId& referenceId) { stream << referenceId; },
            [&stream](const LocalVocabEntry& referenceValue) {
              stream << referenceValue.toStringRepresentation();
            }},
        referenceValue);
  };

  std::stringstream stream;
  stream << "Prefilter RelationalExpression<" << getRelationalOpStr(Comparison)
         << ">\nreferenceValue_ : ";
  referenceValueToString(stream, rightSideReferenceValue_);
  stream << " ." << std::endl;
  return stream.str();
};

// SECTION LOGICAL OPERATIONS
//______________________________________________________________________________
template <LogicalOperator Operation>
std::unique_ptr<PrefilterExpression>
LogicalExpression<Operation>::logicalComplement() const {
  using enum LogicalOperator;
  // Source De-Morgan's laws: De Morgan's laws, Wikipedia.
  // Reference: https://en.wikipedia.org/wiki/De_Morgan%27s_laws
  if constexpr (Operation == OR) {
    // De Morgan's law: not (A or B) = (not A) and (not B)
    return std::make_unique<AndExpression>(child1_->logicalComplement(),
                                           child2_->logicalComplement());
  } else {
    static_assert(Operation == AND);
    // De Morgan's law: not (A and B) = (not A) or (not B)
    return std::make_unique<OrExpression>(child1_->logicalComplement(),
                                          child2_->logicalComplement());
  }
};

//______________________________________________________________________________
template <LogicalOperator Operation>
RelevantBlockRanges LogicalExpression<Operation>::evaluateImpl(
    std::span<const ValueId> idSpan) const {
  using enum LogicalOperator;
  if constexpr (Operation == AND) {
    return getIntersection(child1_->evaluateImpl(idSpan),
                           child2_->evaluateImpl(idSpan));
  } else {
    static_assert(Operation == OR);
    return getUnion(child1_->evaluateImpl(idSpan),
                    child2_->evaluateImpl(idSpan));
  }
};

//______________________________________________________________________________
template <LogicalOperator Operation>
bool LogicalExpression<Operation>::operator==(
    const PrefilterExpression& other) const {
  const auto* otherlogical =
      dynamic_cast<const LogicalExpression<Operation>*>(&other);
  if (!otherlogical) {
    return false;
  }
  return *child1_ == *otherlogical->child1_ &&
         *child2_ == *otherlogical->child2_;
};

//______________________________________________________________________________
template <LogicalOperator Operation>
std::unique_ptr<PrefilterExpression> LogicalExpression<Operation>::clone()
    const {
  return std::make_unique<LogicalExpression<Operation>>(child1_->clone(),
                                                        child2_->clone());
};

//______________________________________________________________________________
template <LogicalOperator Operation>
std::string LogicalExpression<Operation>::asString(size_t depth) const {
  std::string child1Info =
      depth < maxInfoRecursion ? child1_->asString(depth + 1) : "MAX_DEPTH";
  std::string child2Info =
      depth < maxInfoRecursion ? child2_->asString(depth + 1) : "MAX_DEPTH";
  std::stringstream stream;
  stream << "Prefilter LogicalExpression<" << getLogicalOpStr(Operation)
         << ">\n"
         << "child1 {" << child1Info << "}"
         << "child2 {" << child2Info << "}" << std::endl;
  return stream.str();
};

// SECTION NOT-EXPRESSION
//______________________________________________________________________________
std::unique_ptr<PrefilterExpression> NotExpression::logicalComplement() const {
  // Logically we complement (negate) a NOT here => NOT cancels out.
  // Therefore, we can simply return the child of the respective NOT
  // expression after undoing its previous complementation.
  return child_->logicalComplement();
};

//______________________________________________________________________________
RelevantBlockRanges NotExpression::evaluateImpl(
    std::span<const ValueId> idSpan) const {
  return child_->evaluateImpl(idSpan);
};

//______________________________________________________________________________
bool NotExpression::operator==(const PrefilterExpression& other) const {
  const auto* otherNotExpression = dynamic_cast<const NotExpression*>(&other);
  if (!otherNotExpression) {
    return false;
  }
  return *child_ == *otherNotExpression->child_;
}

//______________________________________________________________________________
std::unique_ptr<PrefilterExpression> NotExpression::clone() const {
  return std::make_unique<NotExpression>((child_->clone()), true);
};

//______________________________________________________________________________
std::string NotExpression::asString(size_t depth) const {
  std::string childInfo =
      depth < maxInfoRecursion ? child_->asString(depth + 1) : "MAX_DEPTH";
  std::stringstream stream;
  stream << "Prefilter NotExpression:\n"
         << "child {" << childInfo << "}" << std::endl;
  return stream.str();
}

//______________________________________________________________________________
// Instanitate templates with specializations (for linking accessibility)
template class RelationalExpression<CompOp::LT>;
template class RelationalExpression<CompOp::LE>;
template class RelationalExpression<CompOp::GE>;
template class RelationalExpression<CompOp::GT>;
template class RelationalExpression<CompOp::EQ>;
template class RelationalExpression<CompOp::NE>;

template class LogicalExpression<LogicalOperator::AND>;
template class LogicalExpression<LogicalOperator::OR>;

namespace detail {

//______________________________________________________________________________
// Returns the corresponding mirrored `RelationalExpression<mirrored
// comparison>` for the given `CompOp comparison` template argument. For
// example, the mirroring procedure will transform the relational expression
// `referenceValue > ?var` into `?var < referenceValue`.
template <CompOp comparison>
static std::unique_ptr<PrefilterExpression> makeMirroredExpression(
    const IdOrLocalVocabEntry& referenceValue) {
  using enum CompOp;
  using namespace ad_utility;
  using P = std::pair<CompOp, CompOp>;
  constexpr ConstexprMap<CompOp, CompOp, 6> mirrorMap(
      {P{LT, GT}, P{LE, GE}, P{GE, LE}, P{GT, LT}, P{EQ, EQ}, P{NE, NE}});
  return std::make_unique<RelationalExpression<mirrorMap.at(comparison)>>(
      referenceValue);
}

//______________________________________________________________________________
void checkPropertiesForPrefilterConstruction(
    const std::vector<PrefilterExprVariablePair>& vec) {
  auto viewVariable = vec | ql::views::values;
  if (!ql::ranges::is_sorted(viewVariable, std::less<>{})) {
    throw std::runtime_error(
        "The vector must contain the <PrefilterExpression, Variable> pairs in "
        "sorted order w.r.t. Variable value.");
  }
  if (auto it = ql::ranges::adjacent_find(viewVariable);
      it != ql::ranges::end(viewVariable)) {
    throw std::runtime_error(
        "For each relevant Variable must exist exactly one "
        "<PrefilterExpression, Variable> pair.");
  }
}

//______________________________________________________________________________
template <CompOp comparison>
std::vector<PrefilterExprVariablePair> makePrefilterExpressionVec(
    const IdOrLocalVocabEntry& referenceValue, const Variable& variable,
    const bool mirrored) {
  std::vector<PrefilterExprVariablePair> resVec{};
  resVec.emplace_back(
      mirrored
          ? makeMirroredExpression<comparison>(referenceValue)
          : std::make_unique<RelationalExpression<comparison>>(referenceValue),
      variable);
  return resVec;
}

//______________________________________________________________________________
#define INSTANTIATE_MAKE_PREFILTER(Comparison)                       \
  template std::vector<PrefilterExprVariablePair>                    \
  makePrefilterExpressionVec<Comparison>(const IdOrLocalVocabEntry&, \
                                         const Variable&, const bool);
INSTANTIATE_MAKE_PREFILTER(CompOp::LT);
INSTANTIATE_MAKE_PREFILTER(CompOp::LE);
INSTANTIATE_MAKE_PREFILTER(CompOp::GE);
INSTANTIATE_MAKE_PREFILTER(CompOp::GT);
INSTANTIATE_MAKE_PREFILTER(CompOp::EQ);
INSTANTIATE_MAKE_PREFILTER(CompOp::NE);

}  //  namespace detail
}  //  namespace prefilterExpressions
