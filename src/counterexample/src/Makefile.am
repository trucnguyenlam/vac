AUTOMAKE_OPTIONS = foreign

bin_PROGRAMS = counterexample
counterexample_CFLAGS = -I../../ccl/include/ -static -pthread
counterexample_LDADD = ../../ccl/src/libccl.a -lm
counterexample_SOURCES =  	ARBACLexer.c \
							ARBACParser.c \
							CounterExampleIO.c \
							CounterExamplePhases.c \
							CounterExample.c 

