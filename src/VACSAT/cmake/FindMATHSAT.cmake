set(MATHSAT_PREFIX "${MATHSAT_PREFIX}" CACHE PATH "path ")

find_path(MATHSAT_INCLUDE_DIR mathsat.h
        PATHS ${SOLVER_PREFIX}/include ${MATHSAT_PREFIX}/include /usr/include /usr/local/include NO_DEFAULT_PATH)

find_library(MATHSAT_LIBRARY NAMES mathsat
        PATHS ${SOLVER_PREFIX}/lib ${MATHSAT_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)


if(MATHSAT_INCLUDE_DIR AND MATHSAT_LIBRARY)
    get_filename_component(MATHSAT_LIBRARY_DIR ${MATHSAT_LIBRARY} PATH)
    set(MATHSAT_FOUND TRUE INTERNAL CACHE BOOLEAN "" FORCE)
endif()

if(MATHSAT_FOUND)
    if(NOT MATHSAT_FIND_QUIETLY)
        MESSAGE(STATUS "Found MATHSAT: ${MATHSAT_LIBRARY}")
    endif()
elseif(NOT MATHSAT_FOUND)
    if(MATHSAT_FIND_REQUIRED)
        message(FATAL_ERROR "Could not find MATHSAT")
    endif()
endif()
