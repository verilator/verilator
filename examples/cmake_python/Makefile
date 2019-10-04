######################################################################
#
# DESCRIPTION: Verilator Python cmake example usage
#
# This file shows usage of the Python support using cmake.
# This makefile is here for testing the examples and should
# generally not be added to a project.
#
# Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
######################################################################

# Check if CMake is installed and of correct version
ifeq ($(shell which cmake),)
TARGET := nocmake
else
CMAKE_VERSION := $(shell cmake --version | grep -Po '(\d[\.\d]+)')
CMAKE_MAJOR := $(shell echo $(CMAKE_VERSION) | cut -f1 -d.)
CMAKE_MINOR := $(shell echo $(CMAKE_VERSION) | cut -f2 -d.)
CMAKE_GT_3_8 := $(shell [ $(CMAKE_MAJOR) -gt 3 -o \( $(CMAKE_MAJOR) -eq 3 -a $(CMAKE_MINOR) -ge 8 \) ] && echo true)
ifeq ($(CMAKE_GT_3_8),true)
# Check if pybind11 is available
ifeq (1,${PYBIND11_ROOT}$(shell python3 -m pybind11 >/dev/null 2>&1; echo $$?))
TARGET := nopybind11
else
TARGET := run
endif
else
TARGET := oldcmake
endif
endif

default: $(TARGET)

run:
	@echo
	@echo "-- Verilator Python example using CMake"

	@echo
	@echo "-- CMake ----------------"
	mkdir -p build && cd build && cmake ..

	@echo
	@echo "-- COMPILE -----------------"
	cmake --build build

	@echo
	@echo "-- RUN ---------------------"
	python3 sim_main.py

	@echo
	@echo "-- DONE --------------------"
	@echo

clean mostlyclean distclean maintainer-clean:
	@rm -rf build

nocmake:
	@echo
	@echo "%Skip: CMake has not been found"
	@echo

oldcmake:
	@echo
	@echo "%Skip: CMake version is too old (need at least 3.8)"
	@echo

nopybind11:
	@echo
	@echo "%Skip: Python example disabled because the PYBIND11_ROOT environment variable was not set."
	@echo "%This example can be enabled by installing pybind11 using your system package manager"
	@echo "%or setting the PYBIND11_ROOT environment variable to a local copy."
	@echo
