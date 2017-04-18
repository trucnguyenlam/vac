#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.68])
AC_INIT([VAC2_Translate], [2.0], [trucnguyenlam@gmail.com,enrico.steffinlongo@gmail.com])


#Auxiliary scripts such as install-sh and depcomp should be in
#build-aux. E.g. AC CONFIG AUX DIR([build-aux]).
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE([dist-bzip2])

AC_CONFIG_SRCDIR([../ccl/src/Makefile])
AC_CONFIG_SRCDIR([src/ARBACParser.h])

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX

#AC_CONFIG_HEADERS([config.h])

#AC_CONFIG_MACRO_DIR([m4])
#AX_BOOST_BASE(,, [AC_MSG_ERROR([libfoo needs Boost, but it was not found in your system])])
#AX_BOOST_SYSTEM
#AX_BOOST_FILESYSTEM


# Checks for libraries.
AC_CHECK_LIB([antlr3c], [antlr3AsciiFileStreamNew], [], [
		echo "antlr3c library is required for this program"; exit -1])

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
AC_SUBST([DEFAULT_CXXFLAGS], " -std=c++11 -static -O3 -pthread ")


AC_CONFIG_FILES([Makefile
				 src/Makefile])
AC_OUTPUT
