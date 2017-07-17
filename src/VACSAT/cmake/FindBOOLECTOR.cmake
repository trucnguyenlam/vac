set(BOOLECTOR_PREFIX "${BOOLECTOR_PREFIX}" CACHE PATH "path ")

find_path(BOOLECTOR_INCLUDE_DIR boolector.h
        PATHS ${BOOLECTOR_PREFIX}/include /usr/include /usr/local/include NO_DEFAULT_PATH)

find_path(BOOLECTOR_LIBRARY NAMES libboolector.a
        PATHS ${BOOLECTOR_PREFIX}/lib /usr/lib /usr/local/lib NO_DEFAULT_PATH)

if(BOOLECTOR_INCLUDE_DIR AND BOOLECTOR_LIBRARY)
    get_filename_component(BOOLECTOR_LIBRARY_DIR ${BOOLECTOR_LIBRARY} PATH)
    set(BOOLECTOR_FOUND TRUE)
endif()

if(BOOLECTOR_FOUND)
    if(NOT BOOLECTOR_FIND_QUIETLY)
        MESSAGE(STATUS "Found BOOLECTOR: ${BOOLECTOR_LIBRARY}")
    endif()
elseif(NOT BOOLECTOR_FOUND)
    if(BOOLECTOR_FIND_REQUIRED)
        message(FATAL_ERROR "Could not find BOOLECTOR")
    endif()
endif()
