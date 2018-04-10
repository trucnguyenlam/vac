set(ANTLR4_PREFIX "${ANTLR4_PREFIX}" CACHE PATH "path ")

find_path(ANTLR4_INCLUDE_DIR antlr4-runtime.h
    PATHS ${ANTLR4_PREFIX}/include/antlr4-runtime /usr/include /usr/local/include NO_DEFAULT_PATH)

find_library(ANTLR4_LIBRARY NAMES antlr4-runtime
    PATHS ${ANTLR4_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)

if(ANTLR4_INCLUDE_DIR AND ANTLR4_LIBRARY)
    get_filename_component(ANTLR4_LIBRARY_DIR ${ANTLR4_LIBRARY} PATH)
    set(ANTLR4_FOUND TRUE INTERNAL CACHE BOOLEAN "" FORCE)
endif()

if(ANTLR4_FOUND)
   if(NOT ANTLR4_FIND_QUIETLY)
       message(STATUS "Found ANTLR4: ${ANTLR4_LIBRARY}")
   endif()
elseif(NOT ANTLR4_FOUND)
   if(ANTLR4_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find ANTLR4")
   endif()
endif()
