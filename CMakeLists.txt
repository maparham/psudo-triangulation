# Created by the script cgal_create_CMakeLists
# This is the CMake script for compiling a set of CGAL applications.

project( executable )


cmake_minimum_required(VERSION 2.8.11)

# CGAL and its components
find_package( CGAL QUIET COMPONENTS Qt4 )

if ( NOT CGAL_FOUND )

  message(STATUS "This project requires the CGAL library, and will not be compiled.")
  return()  

endif()

# include helper file
include( ${CGAL_USE_FILE} )


# Boost and its components
find_package( Boost REQUIRED )

if ( NOT Boost_FOUND )

  message(STATUS "This project requires the Boost library, and will not be compiled.")

  return()  

endif()

# include for local directory

# include for local package

# Qt4
set( QT_USE_QTXML     false )
set( QT_USE_QTMAIN    true )
set( QT_USE_QTSCRIPT  false )
set( QT_USE_QTOPENGL  false )

find_package(Qt4)  

if ( NOT QT_FOUND )

  message(STATUS "This project requires the Qt4 library, and will not be compiled.")
  return()  

endif()


# Creating entries for target: executable
# ############################

if ( CGAL_Qt4_FOUND AND QT_FOUND )

  include( ${QT_USE_FILE} )
  include_directories( ${QT_INCLUDE_DIR} )  

  # UI files (Qt Designer files)

  # qrc files (resources files, that contain icons, at least)

  # use the Qt MOC preprocessor on classes that derives from QObject

endif()

#SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a;.so")
#SET(CMAKE_FIND_LIBRARY_PREFIXES "lib")
#SET(BUILD_SHARED_LIBRARIES OFF)
#SET(CMAKE_EXE_LINKER_FLAGS "-static")
	
add_executable( executable  psudo-triangulation.cpp  ${DT_UI_FILES} ${DT_RESOURCE_FILES} )

add_to_cached_list( CGAL_EXECUTABLE_TARGETS executable )

# Link the executable to CGAL and third-party libraries
target_link_libraries(executable  ${QT_LIBRARIES} ${CGAL_LIBRARIES})

