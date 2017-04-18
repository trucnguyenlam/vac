#cmake_minimum_required(VERSION 3.7)
cmake_minimum_required(VERSION 3.5)
project(translate)

set(CMAKE_CXX_STANDARD 11)  # enable C++11 standard
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fpermissive -Wwrite-strings -static")



set(DEPS_DIR "${CMAKE_CURRENT_SOURCE_DIR}/deps")

set(SOURCE_FILES
        src/SMTSolvers/yices.cpp
        src/SMTSolvers/yices.h
        src/SMTSolvers/Z3.cpp
        src/SMTSolvers/Z3.h
        src/_generate.h
        src/ARBAC_to_CBMC_ExactAlg.cpp
        src/ARBAC_to_CompletenessLazyCSeq.cpp
        src/ARBAC_to_ConcurC.cpp
        src/ARBAC_to_ELDARICA_ExactAlg.cpp
        src/ARBAC_to_GETAFIX_ExactAlg.cpp
        src/ARBAC_to_GETAFIX_parallel_ExactAlg.cpp
        src/ARBAC_to_HSF_ExactAlg.cpp
        src/ARBAC_to_INTERPROC_OverApr.cpp
        src/ARBAC_to_LazyCSeq.cpp
        src/ARBAC_to_LazyCSeq_r6.cpp
        src/ARBAC_to_LazyCSeq_r6_ssa.cpp
        src/ARBAC_to_LazyCSeqInlined.cpp
        src/ARBAC_to_MUCKE_CAV.cpp
        src/ARBAC_to_MUCKE_ExactAlg.cpp
        src/ARBAC_to_NuSMV_ExactAlg.cpp
        src/ARBAC_to_smt.cpp
        src/ARBAC_to_SSA.cpp
        src/ARBAC_to_yices.cpp
        src/ARBACAbstract.cpp
        src/ARBACAbstract.h
        src/ARBACData.cpp
        src/ARBACData.h
        src/ARBACExact.cpp
        src/ARBACExact.h
        src/ARBACInfo.cpp
        src/ARBACLexer.cpp
        src/ARBACLexer.h
        src/ARBACParser.cpp
        src/ARBACParser.h
        src/ARBACTool.cpp
        src/ARBACTransform.cpp
        src/ARBACTransform.h
        src/ARBACUtil.cpp
        src/ARBACUtil.h
        #src/comb_norep_lex.cpp
        #src/comb_norep_lex_example.cpp
        src/Logics.cpp
        src/Logics.h
        src/SMT.h
        src/SMT_Pruning.cpp
        src/SMT_Pruning.h
        src/Solvers.h
        src/SSA_Structs.cpp
        src/SSA_Structs.h
        src/varOrd.cpp
        src/varOrd.h
        src/Yices.cpp)



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

# Add include directories for local libraries
include_directories( "${YICES_INCLUDE_DIR}" "${Z3_INCLUDE_DIR}" "${CCL_INCLUDE_DIR}" )

# Add OpenMP (used by Z3)
find_package(OpenMP REQUIRED)
# Set OpenMP flags (BLACK MAGIC)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")

# Add local libraries linking directories
link_directories(${YICES_LIBRARY_DIR} ${Z3_LIBRARY_DIR} ${CCL_LIBRARY_DIR})


add_executable(translate ${SOURCE_FILES})
# Set the link libraries (GMP MUST BE THE LAST)
target_link_libraries(translate yices z3 ccl antlr3c gmp)
