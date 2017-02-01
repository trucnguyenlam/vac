#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.68])
AC_INIT([VAC2_toolchain], [2.0], [trucnguyenlam@gmail.com,enrico.steffinlongo@gmail.com])


#Auxiliary scripts such as install-sh and depcomp should be in
#build-aux. E.g. AC CONFIG AUX DIR([build-aux]).
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE([dist-bzip2])

AC_CONFIG_SRCDIR([src/ccl/src/Makefile])
AC_CONFIG_SRCDIR([src/simplify/src/ARBACParser.h])
AC_CONFIG_SRCDIR([src/translate/src/ARBACParser.h])
AC_CONFIG_SRCDIR([src/counterexample/src/ARBACParser.h])

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX

#AC_CONFIG_HEADERS([config.h])

# Checks for libraries.
AC_CHECK_LIB([antlr3c], [antlr3AsciiFileStreamNew], [], [
		echo "antlr3c library is required for this program"; exit -1])
AC_CHECK_LIB([roxml], [roxml_load_doc], [], [
		echo "roxml library is required for this program"; exit -1])

#AC_CONFIG_SUBDIRS([subdir]) not used since configure is identical

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h unistd.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL

# Checks for library functions.
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_CHECK_FUNCS([memset strdup])


AC_SUBST([DEFAULT_CFLAGS], " -static -O3 -pthread ")
AC_SUBST([DEFAULT_CXXFLAGS], " -static -O3 -pthread ")


AC_CONFIG_FILES([Makefile
				 src/simplify/Makefile
				 src/simplify/src/Makefile
				 src/translate/Makefile
				 src/translate/src/Makefile
				 src/counterexample/Makefile
				 src/counterexample/src/Makefile])
AC_OUTPUT
