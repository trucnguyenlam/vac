#cmake_minimum_required(VERSION 3.7)
cmake_minimum_required(VERSION 3.5)
project(vacsat_old)

set(CMAKE_CXX_STANDARD 11)  # enable C++11 standard

SET(CMAKE_C_COMPILER cc)
SET(CMAKE_CXX_COMPILER c++)

set(PROJECT_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")

# Awfull trick to reset flags in case of sanitizer
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS_BASE}")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Werror -Wno-unused -Wno-comment -Wno-sign-compare -fpermissive -Wwrite-strings")

find_program(GOLD_FOUND gold)
if (GOLD_FOUND)
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=gold")
    message(STATUS "gold found! Faster linking!")
else (GOLD_FOUND)
    message(WARNING "gold not found! Slower linking!")
endif (GOLD_FOUND)


find_program(CCACHE_FOUND ccache)
if (CCACHE_FOUND)
    message(STATUS "ccache found! Faster compilation!")
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE ccache)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK    ccache)
else (CCACHE_FOUND)
    message(WARNING "ccache not found! Slower compilation!")
endif (CCACHE_FOUND)

set(DEPS_DIR "${PROJECT_ROOT}/deps")

set(SOURCE_FILES
        ARBACUtil.h
        ARBACUtil.cpp
        ARBACData.h
        ARBACData.cpp
        ARBACTool.cpp
        ARBACLexer.h
        ARBACLexer.cpp
        ARBACParser.h
        ARBACParser.cpp
        #required by all precise analysis
        ARBACExact.h
        ARBACExact.cpp
        #middle level analysis
        ARBAC_to_ConcurC.cpp
        ARBAC_to_LazyCSeq.cpp
        ARBAC_to_CompletenessLazyCSeq.cpp)

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
        "${PROJECT_ROOT}/cmake")
# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

# Set local prefix for local libraries
set(CCL_PREFIX ${DEPS_DIR}/ccl)
set(ANTLR3C_PREFIX ${DEPS_DIR}/antlr3c)

# For each required library call its find macro
find_package(CCL REQUIRED)
find_package(ANTLR3C REQUIRED)

# Add spdlog library for logging
#set(CMAKE_PREFIX_PATH ${DEPS_DIR}/spdlog)
#find_package(spdlog CONFIG REQUIRED)
#find_package(Threads)


# Add include directories for local libraries
include_directories( "${CCL_INCLUDE_DIR}" "${ANTLR3C_INCLUDE_DIR}" )


# Add local libraries linking directories
link_directories(${CCL_LIBRARY_DIR} ${ANTLR3C_LIBRARY_DIR})


add_library(vacsat_old STATIC ${SOURCE_FILES} )

# Set the link libraries (GMP MUST BE THE LAST)
target_link_libraries(vacsat_old ccl antlr3c)


#install (TARGETS vacsat DESTINATION bin)
