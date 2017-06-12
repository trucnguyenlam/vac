#cmake_minimum_required(VERSION 3.7)
cmake_minimum_required(VERSION 3.5)
project(vacsat)

set(CMAKE_CXX_STANDARD 11)  # enable C++11 standard

#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -fpermissive -Wwrite-strings")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -Wno-unused -Wno-comment -Wno-sign-compare")

find_program(GOLD_FOUND gold)
if (GOLD_FOUND)
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=gold")
    message(STATUS "gold found! Faster linking!")
else (GOLD_FOUND)
    message(WARNING "gold not found! Slower linking!")
endif (GOLD_FOUND)


find_program(CCACHE_FOUND ccache)
if (CCACHE_FOUND)
    message(STATUS "ccache found! Faster compilation!")
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE ccache)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK    ccache)
else (CCACHE_FOUND)
    message(WARNING "ccache not found! Slower compilation!")
endif (CCACHE_FOUND)

set(DEPS_DIR "${CMAKE_CURRENT_SOURCE_DIR}/deps")

set(SOURCE_FILES
        src/ARBACUtil.h
        src/ARBACUtil.cpp
        src/ARBACData.h
        src/ARBACData.cpp
        src/ARBACTool.cpp
        src/ARBACLexer.h
        src/ARBACLexer.cpp
        src/ARBACParser.h
        src/ARBACParser.cpp
        #wanted by all precise analysis
        src/ARBACExact.h
        src/ARBACExact.cpp
        src/SMT.h
        src/SMTSolvers/yices.h
        src/SMTSolvers/yices.cpp
        src/SMTSolvers/Z3.h
        src/SMTSolvers/Z3.cpp
        src/Logics.h
        src/Logics.cpp
        src/SMT_Pruning.h
        src/SMT_Pruning.cpp
        src/ARBAC_to_ConcurC.cpp
        src/ARBAC_to_LazyCSeq.cpp
        src/ARBAC_to_CompletenessLazyCSeq.cpp
        src/SMT_Pruning_R6_LazyCSeq.cpp
        src/SMT_Pruning_R6_SSA.cpp
        src/ARBAC_to_smt.cpp
        src/ARBAC_to_SMT_BMC.cpp
        src/ExprToSmt.h
        src/ARBACTransform.h
        src/ARBACTransform.cpp
        src/Policy.h
        src/Policy.cpp
        src/prelude.h
        src/SMT_Analysis.h
        src/SMT_Analysis.cpp
        src/SMT_Analysis_old_style.cpp
        src/config.h
        src/BMC_Struct.h
        src/ARBAC_to_SMT_BMC.h
        src/config.cpp
        src/SMT_Configuration.h)

set_source_files_properties(src/ARBACParser.cpp PROPERTIES COMPILE_FLAGS "-fpermissive -Wwrite-strings")
set_source_files_properties(src/ARBACParser.h   PROPERTIES COMPILE_FLAGS "-fpermissive -Wwrite-strings")
set_source_files_properties(src/ARBACLexer.cpp  PROPERTIES COMPILE_FLAGS "-fpermissive -Wwrite-strings")
set_source_files_properties(src/ARBACLexer.h    PROPERTIES COMPILE_FLAGS "-fpermissive -Wwrite-strings")


# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
        "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

# Set local prefix for local libraries
set(YICES_PREFIX ${DEPS_DIR}/yices_2.5.2_static)
set(Z3_PREFIX ${DEPS_DIR}/z3_static)
set(CCL_PREFIX ${DEPS_DIR}/ccl)

# For each required library call its find macro
find_package(GMP REQUIRED)
find_package(YICES REQUIRED)
find_package(Z3 REQUIRED)
find_package(CCL REQUIRED)
find_package(ANTLR3C REQUIRED)

# Add spdlog library for logging
set(CMAKE_PREFIX_PATH ${DEPS_DIR}/spdlog)
find_package(spdlog CONFIG REQUIRED)
find_package(Threads)


FIND_PACKAGE( Boost COMPONENTS program_options REQUIRED )
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )

# Add include directories for local libraries
include_directories( "${YICES_INCLUDE_DIR}" "${Z3_INCLUDE_DIR}" "${CCL_INCLUDE_DIR}" )

# Add OpenMP (used by Z3)
find_package(OpenMP REQUIRED)
# Set OpenMP flags (BLACK MAGIC)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")

# Add local libraries linking directories
link_directories(${YICES_LIBRARY_DIR} ${Z3_LIBRARY_DIR} ${CCL_LIBRARY_DIR})

# add external build for antlrcpp
include( ExternalAntlr4Cpp )
# add antrl4cpp artifacts to project environment
include_directories( ${ANTLR4CPP_INCLUDE_DIRS} )
link_directories( ${ANTLR4CPP_LIBS} )
message(STATUS "Found antlr4cpp libs: ${ANTLR4CPP_LIBS} and includes: ${ANTLR4CPP_INCLUDE_DIRS} ")

# include_directories(${PROJECT_SOURCE_DIR}/src)
set(generated_files
    ${PROJECT_SOURCE_DIR}/src/parser/vacgrammarLexer.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/vacgrammarParser.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/vacgrammarBaseListener.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/vacgrammarListener.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/MyListener.cpp
    )

# export generated cpp files into list
foreach(generated_file ${generated_files})
    list(APPEND antlr_generated_files ${generated_file})
    set_source_files_properties(
      ${generated_file}
      PROPERTIES
      COMPILE_FLAGS -Wno-overloaded-virtual
      )
endforeach(generated_file)

set(PARSER_SOURCES
    ${PROJECT_SOURCE_DIR}/src/parser/Logics.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Models.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/translator.cpp
)

add_executable(vacsat ${SOURCE_FILES} ${PARSER_SOURCES} ${antlr_generated_files})
add_dependencies(vacsat antlr4cpp)
# Set the link libraries (GMP MUST BE THE LAST)
target_link_libraries(vacsat antlr4-runtime yices z3 ccl antlr3c gmp ${Boost_LIBRARIES} spdlog::spdlog ${CMAKE_THREAD_LIBS_INIT})


install (TARGETS vacsat DESTINATION bin)
