# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.14

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /home/thomas/Documents/Logiciels/clion/bin/cmake/linux/bin/cmake

# The command to remove a file.
RM = /home/thomas/Documents/Logiciels/clion/bin/cmake/linux/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/thomas/Documents/Projects/smallpiler

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/thomas/Documents/Projects/smallpiler/cmake-build-debug

# Include any dependencies generated for this target.
include CMakeFiles/smallpiler.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/smallpiler.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/smallpiler.dir/flags.make

CMakeFiles/smallpiler.dir/petit-comp.c.o: CMakeFiles/smallpiler.dir/flags.make
CMakeFiles/smallpiler.dir/petit-comp.c.o: ../petit-comp.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/thomas/Documents/Projects/smallpiler/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object CMakeFiles/smallpiler.dir/petit-comp.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/smallpiler.dir/petit-comp.c.o   -c /home/thomas/Documents/Projects/smallpiler/petit-comp.c

CMakeFiles/smallpiler.dir/petit-comp.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/smallpiler.dir/petit-comp.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/thomas/Documents/Projects/smallpiler/petit-comp.c > CMakeFiles/smallpiler.dir/petit-comp.c.i

CMakeFiles/smallpiler.dir/petit-comp.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/smallpiler.dir/petit-comp.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/thomas/Documents/Projects/smallpiler/petit-comp.c -o CMakeFiles/smallpiler.dir/petit-comp.c.s

# Object files for target smallpiler
smallpiler_OBJECTS = \
"CMakeFiles/smallpiler.dir/petit-comp.c.o"

# External object files for target smallpiler
smallpiler_EXTERNAL_OBJECTS =

smallpiler: CMakeFiles/smallpiler.dir/petit-comp.c.o
smallpiler: CMakeFiles/smallpiler.dir/build.make
smallpiler: CMakeFiles/smallpiler.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/thomas/Documents/Projects/smallpiler/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking C executable smallpiler"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/smallpiler.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/smallpiler.dir/build: smallpiler

.PHONY : CMakeFiles/smallpiler.dir/build

CMakeFiles/smallpiler.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/smallpiler.dir/cmake_clean.cmake
.PHONY : CMakeFiles/smallpiler.dir/clean

CMakeFiles/smallpiler.dir/depend:
	cd /home/thomas/Documents/Projects/smallpiler/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/thomas/Documents/Projects/smallpiler /home/thomas/Documents/Projects/smallpiler /home/thomas/Documents/Projects/smallpiler/cmake-build-debug /home/thomas/Documents/Projects/smallpiler/cmake-build-debug /home/thomas/Documents/Projects/smallpiler/cmake-build-debug/CMakeFiles/smallpiler.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/smallpiler.dir/depend

