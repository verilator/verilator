######################################################################
#
# DESCRIPTION: Verilator CMake example usage
#
# This file shows usage of the CMake script.
# This makefile is here for testing the examples and should
# generally not be added to a CMake project.
#
# This file ONLY is placed under the Creative Commons Public Domain, for
# any use, without warranty, 2020 by Wilson Snyder.
# SPDX-License-Identifier: CC0-1.0
#
######################################################################

######################################################################
# Set up variables

# If $VERILATOR_ROOT isn't in the environment, we assume it is part of a
# package install, and verilator is in your path. Otherwise find the
# binary relative to $VERILATOR_ROOT (such as when inside the git sources).

ifeq ($(VERILATOR_ROOT),)
VERILATOR_COVERAGE = verilator_coverage
else
export VERILATOR_ROOT
VERILATOR_COVERAGE = $(VERILATOR_ROOT)/bin/verilator_coverage
endif
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
TARGET := run
else
TARGET := oldcmake
endif
endif

default: $(TARGET)

run:
	@echo
	@echo "-- Verilator CMake hello world example"

	@echo
	@echo "-- VERILATE ----------------"
	mkdir -p build && cd build && cmake ..

	@echo
	@echo "-- BUILD -------------------"
	cmake --build build -j

	@echo
	@echo "-- RUN ---------------------"
	build/example

	@echo
	@echo "-- DONE --------------------"
	@echo

clean mostlyclean distclean maintainer-clean:
	@rm -rf build logs

nocmake:
	@echo
	@echo "%Skip: CMake has not been found"
	@echo

oldcmake:
	@echo
	@echo "%Skip: CMake version is too old (need at least 3.8)"
	@echo
