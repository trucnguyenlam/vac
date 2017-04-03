AUTOMAKE_OPTIONS = foreign

#AM_CPPFLAGS = $(BOOST_CPPFLAGS)

#AM_LDFLAGS = $(BOOST_LDFLAGS)


bin_PROGRAMS = translate
translate_CFLAGS = -I../../ccl/include/ -I../deps/yices_2.5.2_static/include/ -I../deps/z3_static/include/ @DEFAULT_CFLAGS@
translate_CXXFLAGS = -I../../ccl/include/ -I../deps/yices_2.5.2_static/include/ -I../deps/z3_static/include/ @DEFAULT_CXXFLAGS@ -std=c++11 -fpermissive -Wwrite-strings
translate_LDADD = \
            ../../ccl/src/libccl.a \
            ../deps/yices_2.5.2_static/lib/libyices.a \
            ../deps/z3_static/lib/libz3.a \
            -lgmp -lm -lgomp -ldl -lstdc++
# 
# 
#            ../deps/z3_static/lib/libz3.a \
#            $(BOOST_FILESYSTEM_LIB) \
#			$(BOOST_SYSTEM_LIB)


translate_SOURCES =	ARBACData.cpp \
					ARBACLexer.cpp \
					ARBACParser.cpp \
					ARBACTool.cpp \
					ARBACTransform.cpp \
					ARBACUtil.cpp \
					ARBACExact.cpp \
					ARBACAbstract.cpp \
					ARBACInfo.cpp \
					ARBAC_to_GETAFIX_ExactAlg.cpp \
					ARBAC_to_GETAFIX_parallel_ExactAlg.cpp \
					ARBAC_to_MUCKE_ExactAlg.cpp \
					ARBAC_to_MUCKE_CAV.cpp \
					ARBAC_to_ConcurC.cpp \
					ARBAC_to_CBMC_ExactAlg.cpp \
					ARBAC_to_INTERPROC_OverApr.cpp \
					ARBAC_to_HSF_ExactAlg.cpp \
					ARBAC_to_ELDARICA_ExactAlg.cpp \
					ARBAC_to_SMT2_ExactAlg.cpp \
					ARBAC_to_NuSMV_ExactAlg.cpp \
					ARBAC_to_LazyCSeq.cpp \
					ARBAC_to_LazyCSeqInlined.cpp \
					ARBAC_to_SSA.cpp \
					ARBAC_to_yices.cpp \
					ARBAC_to_CompletenessLazyCSeq.cpp \
					ARBAC_to_smt.cpp \
					SSA_Structs.cpp \
					SMTSolvers/yices.cpp \
					SMTSolvers/Z3.cpp \
					SMT_Pruning.cpp \
					Logics.cpp \
					Yices.cpp \
					varOrd.cpp

