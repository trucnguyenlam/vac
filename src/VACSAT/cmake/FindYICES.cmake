set(YICES_PREFIX "${YICES_PREFIX}" CACHE PATH "path ")

find_path(YICES_INCLUDE_DIR yices.h
    PATHS ${SOLVER_PREFIX}/include ${YICES_PREFIX}/include /usr/include /usr/local/include NO_DEFAULT_PATH)

find_library(YICES_LIBRARY NAMES yices
    PATHS ${SOLVER_PREFIX}/lib ${YICES_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)


if(YICES_INCLUDE_DIR AND YICES_LIBRARY)
    get_filename_component(YICES_LIBRARY_DIR ${YICES_LIBRARY} PATH)
    set(YICES_FOUND TRUE INTERNAL CACHE BOOLEAN "" FORCE)
endif()

if(YICES_FOUND)
   if(NOT YICES_FIND_QUIETLY)
      MESSAGE(STATUS "Found YICES: ${YICES_LIBRARY}")
   endif()
elseif(NOT YICES_FOUND)
   if(YICES_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find YICES")
   endif()
endif()
