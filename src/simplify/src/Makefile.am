AUTOMAKE_OPTIONS = foreign

bin_PROGRAMS = simplify
simplify_CFLAGS = -I../../ccl/include/ @DEFAULT_CFLAGS@
simplify_LDADD = ../../ccl/src/libccl.a -lm
simplify_SOURCES = ARBACReduceAdmin.c \
			ARBACPreCheck.c \
			ARBACImmaterial.c \
			ARBACPruning.c \
			ARBACSlicing.c \
			ARBACLexer.c \
			ARBACParser.c \
			ARBACUtil.c \
			ARBACIO.c
