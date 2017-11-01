#cmake_minimum_required(VERSION 3.7)
cmake_minimum_required(VERSION 3.0)
project(vacsat)

set(CMAKE_CXX_STANDARD 11)  # enable C++11 standard

#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -fpermissive -Wwrite-strings")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -Wno-unused -Wno-unused-parameter -Wno-comment -Wno-sign-compare -Wno-c++1z-extensions -static")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-write-strings -Wall -Wextra -Werror -Wno-unused -Wno-unused-parameter -Wno-comment -Wno-sign-compare -static")

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
        src/SMT.h
        src/SMTSolvers/yices.h
        src/SMTSolvers/yices.cpp
        src/SMTSolvers/Z3.h
        src/SMTSolvers/Z3.cpp
        src/SMTSolvers/boolector.h
        src/SMTSolvers/boolector.cpp
        src/SMTSolvers/mathsat.h
        src/SMTSolvers/mathsat.cpp
        src/Logics.h
        src/Logics.cpp
        src/SMT_Pruning.h
        src/SMT_Pruning.cpp
        src/SMT_Pruning_R6_LazyCSeq.cpp
        src/SMT_Pruning_R6_SSA.cpp
#        src/ARBAC_to_smt.cpp
        src/SMT_BMC.cpp
        src/ARBACTransform.h
        src/ARBACTransform.cpp
        src/Policy.h
        src/Policy.cpp
        src/prelude.h
        src/SMT_Analysis.h
        src/SMT_Analysis.cpp
        src/config.h
        src/SMT_BMC_Struct.h
        src/SMT_Analysis_functions.h
        src/config.cpp
        src/SMT_Configuration.h
        src/SMT_Infini_admin_bmc.cpp
        src/SMT_Overapprox.cpp
        src/SMT_Overapprox_extended.cpp
        src/SMT_Overapprox_super.cpp )

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
        "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

# Set local prefix for local libraries
set(ANTLR3C_PREFIX ${DEPS_DIR}/antlr3c)
set(YICES_PREFIX ${DEPS_DIR}/yices_2.5.2_static)
set(Z3_PREFIX ${DEPS_DIR}/z3_static)
set(CCL_PREFIX ${DEPS_DIR}/ccl)
set(BOOLECTOR_PREFIX ${DEPS_DIR}/boolector)
set(MATHSAT_PREFIX ${DEPS_DIR}/mathsat)

# For each required library call its find macro
find_package(ANTLR3C REQUIRED)
find_package(GMP REQUIRED)
find_package(YICES REQUIRED)
find_package(MATHSAT REQUIRED)
find_package(Z3 REQUIRED)
find_package(BOOLECTOR REQUIRED)
find_package(CCL REQUIRED)

# Add spdlog library for logging
set(CMAKE_PREFIX_PATH ${DEPS_DIR}/spdlog)
find_package(spdlog CONFIG REQUIRED)
find_package(Threads)


FIND_PACKAGE( Boost COMPONENTS program_options REQUIRED )
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )

# Add include directories for local libraries
include_directories("${YICES_INCLUDE_DIR}"
                    "${Z3_INCLUDE_DIR}"
                    "${BOOLECTOR_INCLUDE_DIR}"
                    "${MATHSAT_INCLUDE_DIR}"
                    "${CCL_INCLUDE_DIR}"
                    "${ANTLR3C_INCLUDE_DIR}")

# Add OpenMP (used by Z3)
find_package(OpenMP REQUIRED)
# Set OpenMP flags (BLACK MAGIC)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
# Otherwise use this
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fopenmp")

# Add local libraries linking directories
link_directories(${YICES_LIBRARY_DIR}
                 ${Z3_LIBRARY_DIR}
                 ${BOOLECTOR_LIBRARY}
                 ${MATHSAT_LIBRARY}
                 ${CCL_LIBRARY_DIR}
                 ${ANTLR3C_LIBRARY_DIR})

set(PARSER_SOURCES
    ${PROJECT_SOURCE_DIR}/src/parser/Logics.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Models.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Tokens.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Lexer.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Parser.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/translator.cpp
)

add_executable(vacsat ${SOURCE_FILES} ${PARSER_SOURCES})
add_subdirectory(src/old_parser)
# Set the link libraries (GMP MUST BE THE LAST)
target_link_libraries(vacsat PRIVATE vacsat_old)
target_link_libraries(vacsat PUBLIC yices z3 boolector lgl mathsat gmpxx gmp stdc++)
target_link_libraries(vacsat PUBLIC ccl antlr3c ${Boost_LIBRARIES} spdlog::spdlog ${CMAKE_THREAD_LIBS_INIT})


install (TARGETS vacsat DESTINATION bin)
