add_library(httpParser AcceptHeaderQleverVisitor.h AcceptHeaderQleverVisitor.cpp
        generated/AcceptHeaderBaseListener.h generated/AcceptHeaderBaseListener.cpp
        generated/AcceptHeaderLexer.h generated/AcceptHeaderLexer.cpp
        generated/AcceptHeaderListener.h generated/AcceptHeaderListener.cpp
        generated/AcceptHeaderParser.h generated/AcceptHeaderParser.cpp
        generated/AcceptHeaderVisitor.h generated/AcceptHeaderVisitor.cpp)
qlever_target_link_libraries(httpParser antlr4_static util)
target_precompile_headers(httpParser PRIVATE "${antlr_SOURCE_DIR}/runtime/Cpp/runtime/src/antlr4-runtime.h")
