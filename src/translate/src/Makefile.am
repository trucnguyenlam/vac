AUTOMAKE_OPTIONS = foreign

bin_PROGRAMS = translate
translate_CFLAGS = -I../../ccl/include/ -static
translate_LDADD = ../../ccl/lib/libccl.a -lm
translate_SOURCES =	ARBACLexer.c \
					ARBACParser.c \
					ARBACTool.c \
					ARBACTransform.c \
					ARBACUtil.c \
					ARBACExact.c \
					ARBACAbstract.c \
					ARBAC_to_GETAFIX_ExactAlg.c \
					ARBAC_to_GETAFIX_parallel_ExactAlg.c \
					ARBAC_to_MUCKE_ExactAlg.c \
					ARBAC_to_MUCKE_CAV.c \
					ARBAC_to_LazyCSeq.c \
					ARBAC_to_ConcurC.c \
					ARBAC_to_CBMC_ExactAlg.c \
					ARBAC_to_INTERPROC_OverApr.c \
					ARBAC_to_HSF_ExactAlg.c \
					ARBAC_to_ELDARICA_ExactAlg.c \
					ARBAC_to_SMT2_ExactAlg.c \
					ARBAC_to_NuSMV_ExactAlg.c \
					varOrd.c

