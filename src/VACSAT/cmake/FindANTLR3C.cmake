set(ANTLR3C_PREFIX "${ANTLR3C_PREFIX}" CACHE PATH "path ")


find_path(ANTLR3C_INCLUDE_DIR antlr3.h
    PATHS ${ANTLR3C_PREFIX}/include /usr/include /usr/local/include NO_DEFAULT_PATH)

find_library(ANTLR3C_LIBRARY NAMES antlr3c
    PATHS ${ANTLR3C_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)


if(ANTLR3C_INCLUDE_DIR AND ANTLR3C_LIBRARY)
    get_filename_component(ANTLR3C_LIBRARY_DIR ${ANTLR3C_LIBRARY} PATH)
    set(ANTLR3C_FOUND TRUE INTERNAL CACHE BOOLEAN "" FORCE)
endif()

if(ANTLR3C_FOUND)
   if(NOT ANTLR3C_FIND_QUIETLY)
      MESSAGE(STATUS "Found ANTLR3C: ${ANTLR3C_LIBRARY}")
   endif()
elseif(NOT ANTLR3C_FOUND)
   if(ANTLR3C_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find ANTLR3C")
   endif()
endif()
