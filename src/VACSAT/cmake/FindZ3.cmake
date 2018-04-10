set(Z3_PREFIX "${Z3_PREFIX}" CACHE PATH "path ")

find_path(Z3_INCLUDE_DIR z3++.h
    PATHS ${SOLVER_PREFIX}/include ${Z3_PREFIX}/include /usr/include /usr/local/include NO_DEFAULT_PATH)

find_library(Z3_LIBRARY NAMES z3
    PATHS ${SOLVER_PREFIX}/lib ${Z3_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)


if(Z3_INCLUDE_DIR AND Z3_LIBRARY)
    get_filename_component(Z3_LIBRARY_DIR ${Z3_LIBRARY} PATH)
    set(Z3_FOUND TRUE INTERNAL CACHE BOOLEAN "" FORCE)
endif()

if(Z3_FOUND)
   if(NOT Z3_FIND_QUIETLY)
      MESSAGE(STATUS "Found Z3: ${Z3_LIBRARY}")
   endif()
elseif(NOT Z3_FOUND)
   if(Z3_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find Z3")
   endif()
endif()
