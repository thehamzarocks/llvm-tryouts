# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.7

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
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/thehamzarocks/Downloads/llvm-pass-skeleton

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton

# Include any dependencies generated for this target.
include skeleton/CMakeFiles/SkeletonPass.dir/depend.make

# Include the progress variables for this target.
include skeleton/CMakeFiles/SkeletonPass.dir/progress.make

# Include the compile flags for this target's objects.
include skeleton/CMakeFiles/SkeletonPass.dir/flags.make

skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o: skeleton/CMakeFiles/SkeletonPass.dir/flags.make
skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o: BBlock.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o"
	cd /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton && /usr/bin/c++   $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/SkeletonPass.dir/BBlock.cpp.o -c /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/BBlock.cpp

skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/SkeletonPass.dir/BBlock.cpp.i"
	cd /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/BBlock.cpp > CMakeFiles/SkeletonPass.dir/BBlock.cpp.i

skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/SkeletonPass.dir/BBlock.cpp.s"
	cd /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/BBlock.cpp -o CMakeFiles/SkeletonPass.dir/BBlock.cpp.s

skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.requires:

.PHONY : skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.requires

skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.provides: skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.requires
	$(MAKE) -f skeleton/CMakeFiles/SkeletonPass.dir/build.make skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.provides.build
.PHONY : skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.provides

skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.provides.build: skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o


# Object files for target SkeletonPass
SkeletonPass_OBJECTS = \
"CMakeFiles/SkeletonPass.dir/BBlock.cpp.o"

# External object files for target SkeletonPass
SkeletonPass_EXTERNAL_OBJECTS =

skeleton/libSkeletonPass.so: skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o
skeleton/libSkeletonPass.so: skeleton/CMakeFiles/SkeletonPass.dir/build.make
skeleton/libSkeletonPass.so: skeleton/CMakeFiles/SkeletonPass.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX shared module libSkeletonPass.so"
	cd /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/SkeletonPass.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
skeleton/CMakeFiles/SkeletonPass.dir/build: skeleton/libSkeletonPass.so

.PHONY : skeleton/CMakeFiles/SkeletonPass.dir/build

skeleton/CMakeFiles/SkeletonPass.dir/requires: skeleton/CMakeFiles/SkeletonPass.dir/BBlock.cpp.o.requires

.PHONY : skeleton/CMakeFiles/SkeletonPass.dir/requires

skeleton/CMakeFiles/SkeletonPass.dir/clean:
	cd /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton && $(CMAKE_COMMAND) -P CMakeFiles/SkeletonPass.dir/cmake_clean.cmake
.PHONY : skeleton/CMakeFiles/SkeletonPass.dir/clean

skeleton/CMakeFiles/SkeletonPass.dir/depend:
	cd /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/thehamzarocks/Downloads/llvm-pass-skeleton /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton /home/thehamzarocks/Downloads/llvm-pass-skeleton/skeleton/skeleton/CMakeFiles/SkeletonPass.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : skeleton/CMakeFiles/SkeletonPass.dir/depend
