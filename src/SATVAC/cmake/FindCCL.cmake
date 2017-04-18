set(CCL_PREFIX "${CCL_PREFIX}" CACHE PATH "path ")


find_path(CCL_INCLUDE_DIR containers.h
    PATHS ${CCL_PREFIX}/include /usr/include /usr/local/include )

find_library(CCL_LIBRARY NAMES ccl
    PATHS ${CCL_PREFIX}/lib /usr/lib /usr/local/lib)


if(CCL_INCLUDE_DIR AND CCL_LIBRARY)
    get_filename_component(CCL_LIBRARY_DIR ${CCL_LIBRARY} PATH)
    set(CCL_FOUND TRUE)
endif()

if(CCL_FOUND)
   if(NOT CCL_FIND_QUIETLY)
      MESSAGE(STATUS "Found CCL: ${CCL_LIBRARY}")
   endif()
elseif(NOT CCL_FOUND)
   if(CCL_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find CCL")
   endif()
endif()
