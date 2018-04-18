#cmake_minimum_required(VERSION 3.7)
cmake_minimum_required(VERSION 3.0)

function(find_solver SOLVER_NAME SOLVER_STATUS)
    message(STATUS "${SOLVER_NAME}: ${SOLVER_STATUS}")
    if ((SOLVER_STATUS STREQUAL REQUIRED) OR (SOLVER_STATUS STREQUAL R))
        message(STATUS "Forced to use ${SOLVER_NAME}")
        find_package(${SOLVER_NAME} REQUIRED)
    elseif((SOLVER_STATUS STREQUAL OPTIONAL) OR (SOLVER_STATUS STREQUAL O))
        find_package(${SOLVER_NAME})
    elseif((SOLVER_STATUS STREQUAL EXCLUDED) OR (SOLVER_STATUS STREQUAL E))
        message(STATUS "${SOLVER_NAME} excluded from the build")
    else()
        message(FATAL_ERROR "Wrong specification for SOLVER_NAME")
    endif()
endfunction(find_solver)

project(vacsat)

set(CMAKE_CXX_STANDARD 14)  # enable C++14 standard

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} \
                     -Wno-write-strings \
                     -Wall \
                     -Wextra \
                     -Werror \
                     -Wno-unused \
                     -Wno-unused-parameter \
                     -Wno-comment \
                     -Wno-sign-compare \
                     -Wno-ignored-qualifiers \
                     -Wno-deprecated \
                     -ftemplate-backtrace-limit=0 ")

# SET SPECIFIC FLAGS FOR EACH COMPILER
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
    message(STATUS "using Clang")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-parentheses-equality")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
    message(STATUS "using GCC")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Intel")
    message(STATUS "using Intel C++")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "MSVC")
    message(STATUS "using Visual Studio C++")
endif()

# IF USING GNU GCC
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
#    TRY TO USE GOLD AS LINKER (FASTER) INSTEAD OF LD
    find_program(GOLD_FOUND gold)
    if (GOLD_FOUND)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=gold")
        message(STATUS "gold found! Faster linking!")
    else (GOLD_FOUND)
        message(WARNING "gold not found! Slower linking!")
    endif (GOLD_FOUND)
endif()

# TRY TO USE CCACHE FOR FASTER COMPILATION
find_program(CCACHE_FOUND ccache)
if (CCACHE_FOUND)
    message(STATUS "ccache found! Faster compilation!")
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE ccache)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK    ccache)
else (CCACHE_FOUND)
    message(WARNING "ccache not found! Slower compilation!")
endif (CCACHE_FOUND)


set(STATIC OFF CACHE BOOL "Make statically linked binary") #OFF by default
set(ENABLE_GPL ON CACHE BOOL "permit GPL dependences, if available") #ON by default

set(BOOLECTOR OPTIONAL CACHE STRING "Force to use BOOLECTOR SMT backend ((R)EQUIRED|(O)PTIONAL|(E)XCLUDED) (DEFAULT O)")
set_property(CACHE BOOLECTOR PROPERTY STRINGS REQUIRED OPTIONAL EXCLUDED)

set(YICES OPTIONAL CACHE STRING "Force to use YICES SMT backend ((R)EQUIRED|(O)PTIONAL|(E)XCLUDED) (DEFAULT O)")
set_property(CACHE YICES PROPERTY STRINGS REQUIRED OPTIONAL EXCLUDED)

set(MATHSAT OPTIONAL CACHE STRING "Force to use MATHSAT SMT backend ((R)EQUIRED|(O)PTIONAL|(E)XCLUDED) (DEFAULT O)")
set_property(CACHE MATHSAT PROPERTY STRINGS REQUIRED OPTIONAL EXCLUDED)

set(CVC4 OPTIONAL CACHE STRING "Force to use CVC4 SMT backend ((R)EQUIRED|(O)PTIONAL|(E)XCLUDED) (DEFAULT O)")
set_property(CACHE CVC4 PROPERTY STRINGS REQUIRED OPTIONAL EXCLUDED)

#unset(STATIC CACHE) # <---- this is the important!!

if (STATIC)
    message(STATUS "Making statically linked binary")
    # If STATIC requires only .a libs
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static")
    set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
endif(STATIC)


set(DEPS_DIR "${CMAKE_CURRENT_SOURCE_DIR}/deps")

set(SOURCE_FILES
        src/SMT.h
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
        src/prelude.cpp
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
        src/SMT_Overapprox_super.cpp
        src/SMT_Overapprox_admin.cpp
        src/over_structures.h
        src/over_skeleton.cpp
        src/over_structures.cpp)


# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
        "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
# put static libraries first


# Set local prefix for local libraries
set(ANTLR3C_PREFIX ${DEPS_DIR}/antlr3c)
set(CCL_PREFIX ${DEPS_DIR}/ccl)
#set(BOOLECTOR_PREFIX ${DEPS_DIR}/boolector)
#set(MATHSAT_PREFIX ${DEPS_DIR}/mathsat)
# FIXME: REMOVE THIS
set(SOLVER_PREFIX /home/esteffin/solvers)

# For each required library call its find macro
find_package(ANTLR3C REQUIRED)
find_package(Z3 REQUIRED)
find_solver(BOOLECTOR ${BOOLECTOR})

# Look for GPL solvers only if required
if (ENABLE_GPL)
        find_solver(YICES ${YICES})
        find_solver(MATHSAT ${MATHSAT})
        find_solver(CVC4 ${CVC4})
    if(YICES_FOUND OR MATHSAT_FOUND OR CVC4_FOUND)
        find_package(GMP REQUIRED)
    endif()
endif()
find_package(CCL REQUIRED)

# Set compilation flags for each solver
if (Z3_FOUND)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_Z3")
        set(SOLVER_SOURCES
                ${SOLVER_SOURCES}
                src/SMTSolvers/Z3.h
                src/SMTSolvers/Z3.cpp)
    include_directories("${Z3_INCLUDE_DIR}")
    link_directories("${Z3_LIBRARY_DIR}")
endif()
if (BOOLECTOR_FOUND)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_BOOLECTOR")
    set(SOLVER_SOURCES
            ${SOLVER_SOURCES}
            src/SMTSolvers/boolector.h
                src/SMTSolvers/boolector.cpp)
    include_directories("${BOOLECTOR_INCLUDE_DIR}")
    link_directories("${BOOLECTOR_LIBRARY_DIR}")
endif()
if (YICES_FOUND)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_YICES")
    set(SOLVER_SOURCES
            ${SOLVER_SOURCES}
            src/SMTSolvers/yices.h
                src/SMTSolvers/yices.cpp)
    include_directories("${YICES_INCLUDE_DIR}")
    link_directories("${YICES_LIBRARY_DIR}")
endif()
if (MATHSAT_FOUND)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_MATHSAT")
    set(SOLVER_SOURCES
            ${SOLVER_SOURCES}
            src/SMTSolvers/mathsat.h
            src/SMTSolvers/mathsat.cpp)
    include_directories("${MATHSAT_INCLUDE_DIR}")
    link_directories("${MATHSAT_LIBRARY_DIR}")
endif()
if (CVC4_FOUND)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DUSE_CVC4")
    set(SOLVER_SOURCES
            ${SOLVER_SOURCES}
            src/SMTSolvers/cvc4.h
            src/SMTSolvers/cvc4.cpp)
    include_directories("${CVC4_INCLUDE_DIR}")
    link_directories("${CVC4_LIBRARY_DIR}")
endif()

# Add spdlog library for logging
set(CMAKE_PREFIX_PATH ${DEPS_DIR}/spdlog)
find_package(spdlog CONFIG REQUIRED)
find_package(Threads)


FIND_PACKAGE( Boost COMPONENTS program_options REQUIRED )
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )

# Add include directories for local libraries
include_directories("${CCL_INCLUDE_DIR}"
                    "${ANTLR3C_INCLUDE_DIR}")

# Add OpenMP (used by Z3)
#find_package(OpenMP REQUIRED)
# Set OpenMP flags (BLACK MAGIC)
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
# Otherwise use this
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fopenmp")

# Add local libraries linking directories
link_directories(${CCL_LIBRARY_DIR}
                 ${ANTLR3C_LIBRARY_DIR})

set(PARSER_SOURCES
    ${PROJECT_SOURCE_DIR}/src/parser/Logics.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Models.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Tokens.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Lexer.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/Parser.cpp
    ${PROJECT_SOURCE_DIR}/src/parser/translator.cpp
)


add_executable(vacsat ${SOURCE_FILES} ${SOLVER_SOURCES} ${PARSER_SOURCES})
add_subdirectory(src/old_parser)
# Set the link libraries (GMP MUST BE THE LAST)
# Set compilation flags for each solver
if (Z3_FOUND)
    target_link_libraries(vacsat PUBLIC z3)
endif()
if (BOOLECTOR_FOUND)
    target_link_libraries(vacsat PUBLIC boolector lgl)
endif()
if (YICES_FOUND)
    target_link_libraries(vacsat PUBLIC yices)
endif()
if (MATHSAT_FOUND)
    target_link_libraries(vacsat PUBLIC mathsat)
endif()
if (CVC4_FOUND)
    target_link_libraries(vacsat PUBLIC cvc4)
endif()
if(YICES_FOUND OR MATHSAT_FOUND OR CVC4_FOUND)
    target_link_libraries(vacsat PUBLIC gmp)
endif()


#include(cotire)
#cotire(vacsat)

# cotire sets the following properties
#get_target_property(_unitySource vacsat COTIRE_CXX_UNITY_SOURCE)
#get_target_property(_prefixHeader vacsat COTIRE_CXX_PREFIX_HEADER)
#get_target_property(_precompiledHeader vacsat COTIRE_CXX_PRECOMPILED_HEADER)
#get_target_property(_unityTargetName vacsat COTIRE_UNITY_TARGET_NAME)

#if (_unitySource)
#	message(STATUS "example unity source: ${_unitySource}")
#endif()
#if (_prefixHeader)
#	message(STATUS "example prefix header: ${_prefixHeader}")
#endif()
#if (_precompiledHeader)
#	message(STATUS "example precompiled header: ${_precompiledHeader}")
#endif()
#if (TARGET ${_unityTargetName})
#	message(STATUS "example unity target: ${_unityTargetName}")
#endif()


target_link_libraries(vacsat PRIVATE vacsat_old)
#target_link_libraries(vacsat PUBLIC       gmpxx  stdc++)
target_link_libraries(vacsat PUBLIC ccl antlr3c ${Boost_LIBRARIES} spdlog::spdlog ${CMAKE_THREAD_LIBS_INIT})


install (TARGETS vacsat DESTINATION bin)
