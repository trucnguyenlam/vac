set(CVC4_PREFIX "${CVC4_PREFIX}" CACHE PATH "path ")

find_path(CVC4_INCLUDE_DIR cvc4/cvc4.h
    PATHS ${SOLVER_PREFIX}/include ${CVC4_PREFIX}/include /usr/include /usr/local/include NO_DEFAULT_PATH)

find_library(CVC4_LIBRARY NAMES cvc4
    PATHS ${SOLVER_PREFIX}/lib ${CVC4_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)


if(CVC4_INCLUDE_DIR AND CVC4_LIBRARY)
    get_filename_component(CVC4_LIBRARY_DIR ${CVC4_LIBRARY} PATH)
    set(CVC4_FOUND TRUE INTERNAL CACHE BOOLEAN "" FORCE)
endif()

if(CVC4_FOUND)
   if(NOT CVC4_FIND_QUIETLY)
      MESSAGE(STATUS "Found CVC4: ${CVC4_LIBRARY}")
   endif()
elseif(NOT CVC4_FOUND)
   if(CVC4_FIND_REQUIRED)
      message(FATAL_ERROR "Could not find CVC4")
   endif()
endif()
