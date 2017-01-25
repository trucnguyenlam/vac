#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.68])
AC_INIT([counterExample,simplify,translate], [2.0], [trucnguyenlam@gmail.com,enrico.steffinlongo@gmail.com])
AM_INIT_AUTOMAKE
AC_CONFIG_SRCDIR([ccl/src/Makefile])
AC_CONFIG_SRCDIR([simplify/src/ARBACParser.h])
AC_CONFIG_SRCDIR([translate/src/ARBACParser.h])
AC_CONFIG_SRCDIR([counterexample/src/ARBACParser.h])

#AC_CONFIG_HEADERS([config.h])

# Checks for programs.
AC_PROG_CC

# Checks for libraries.
AC_CHECK_LIB([antlr3c], [antlr3AsciiFileStreamNew], [], [
		echo "antlr3c library is required for this program"; exit -1])
AC_CHECK_LIB([roxml], [roxml_load_doc], [], [
		echo "roxml library is required for this program"; exit -1])

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL

# Checks for library functions.
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_CHECK_FUNCS([memset strdup])


AC_CONFIG_FILES([Makefile
				 simplify/Makefile
				 simplify/src/Makefile
				 translate/Makefile
				 translate/src/Makefile
				 counterexample/Makefile
				 counterexample/src/Makefile])
AC_OUTPUT
