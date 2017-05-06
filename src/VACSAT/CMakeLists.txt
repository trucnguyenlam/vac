#cmake_minimum_required(VERSION 3.7)
cmake_minimum_required(VERSION 3.5)
project(vacsat)

set(CMAKE_CXX_STANDARD 11)  # enable C++11 standard
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fpermissive -Wwrite-strings -static")



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
        #wanted by Interproc
        src/ARBACAbstract.h
        src/ARBACAbstract.cpp
        #wanted by Mucke
        src/varOrd.h
        src/varOrd.cpp
        src/ARBACInfo.cpp
        src/SMT.h
        src/SMTSolvers/yices.h
        src/SMTSolvers/yices.cpp
        src/SMTSolvers/Z3.h
        src/SMTSolvers/Z3.cpp
        src/Logics.h
        src/Logics.cpp
        src/SMT_Pruning.h
        src/SMT_Pruning.cpp
        src/ARBAC_to_INTERPROC_OverApr.cpp
        src/ARBAC_to_CBMC_ExactAlg.cpp
        src/ARBAC_to_GETAFIX_ExactAlg.cpp
        src/ARBAC_to_NuSMV_ExactAlg.cpp
        src/ARBAC_to_MUCKE_CAV.cpp
        src/ARBAC_to_MUCKE_ExactAlg.cpp
        src/ARBAC_to_ConcurC.cpp
        src/ARBAC_to_LazyCSeq.cpp
        src/ARBAC_to_LazyCSeqInlined.cpp
        src/ARBAC_to_CompletenessLazyCSeq.cpp
        src/SMT_Pruning_R6_LazyCSeq.cpp
        src/SMT_Pruning_R6_SSA.cpp
        src/ARBAC_to_smt.cpp
#        Moved to old_encodings and removed from project
#        src/SSA_Structs.h
#        src/SSA_Structs.cpp
#        src/Solvers.h
#        src/Yices.cpp
#        src/ARBAC_to_SSA.cpp
        src/ExprToSmt.h
        src/ARBACTransform.h
        src/ARBACTransform.cpp
        src/Policy.h
        src/Policy.cpp src/prelude.h)



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


add_executable(vacsat ${SOURCE_FILES})
# Set the link libraries (GMP MUST BE THE LAST)
target_link_libraries(vacsat yices z3 ccl antlr3c gmp)

install (TARGETS vacsat DESTINATION bin)
