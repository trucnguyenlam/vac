#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.68])
AC_INIT([Translate], [1.0], [trucnguyenlam@gmail.com])

AM_INIT_AUTOMAKE

AC_CONFIG_SRCDIR([src/ARBACParser.h])
#AC_CONFIG_HEADERS([config.h])

# Checks for programs.
AC_PROG_CC

# Checks for libraries.
# FIXME: Replace `main' with a function in `-lantlr3c':
AC_CHECK_LIB([antlr3c], [antlr3AsciiFileStreamNew], [], [
		echo "antlr3c library is required for this program"
        exit -1])

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL

# Checks for library functions.
AC_FUNC_MALLOC
AC_FUNC_REALLOC
AC_CHECK_FUNCS([memset strdup])

AC_SUBST([DEFAULT_CFLAGS], " -static -O3 -pthread ")

AC_CONFIG_FILES([Makefile
                 src/Makefile])
AC_OUTPUT
