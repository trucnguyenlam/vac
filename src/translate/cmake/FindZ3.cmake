set(Z3_PREFIX "" CACHE PATH "path ")


find_path(Z3_INCLUDE_DIR z3pp.h
    PATHS ${Z3_PREFIX}/include /usr/include /usr/local/include )

find_library(Z3_LIBRARY NAMES z3
    PATHS ${Z3_PREFIX}/lib /usr/lib /usr/local/lib)


if(Z3_INCLUDE_DIR AND Z3_LIBRARY)
    get_filename_component(Z3_LIBRARY_DIR ${Z3_LIBRARY} PATH)
    set(Z3_FOUND TRUE)
endif()

if(Z3_FOUND)
   if(NOT Z3_FIND_QUIETLY)
      MESSAGE(STATUS "Found Z3: ${Z3_LIBRARY}")
   endif()
elseif(Z3_FOUND)
   if(Z3_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find Z3")
   endif()
endif()
