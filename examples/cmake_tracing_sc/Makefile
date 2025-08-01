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
  VERILATOR = verilator
  VERILATOR_COVERAGE = verilator_coverage
else
  export VERILATOR_ROOT
  VERILATOR = $(VERILATOR_ROOT)/bin/verilator
  VERILATOR_COVERAGE = $(VERILATOR_ROOT)/bin/verilator_coverage
endif
######################################################################

# Check if CMake is installed and of correct version
ifeq ($(shell which cmake),)
  TARGET := nocmake
else
  CMAKE_VERSION := $(shell cmake --version | grep -o '[0-9][.0-9]\+')
  CMAKE_MAJOR := $(shell echo $(CMAKE_VERSION) | cut -f1 -d.)
  CMAKE_MINOR := $(shell echo $(CMAKE_VERSION) | cut -f2 -d.)
  CMAKE_GT_3_8 := $(shell [ $(CMAKE_MAJOR) -gt 3 -o \( $(CMAKE_MAJOR) -eq 3 -a $(CMAKE_MINOR) -ge 8 \) ] && echo true)
  ifneq ($(CMAKE_GT_3_8),true)
    TARGET := oldcmake
  else
    # Check if SC exists via a verilator call (empty if not)
    SYSTEMC_EXISTS := $(shell $(VERILATOR) --get-supported SYSTEMC)

    # Test whether SystemC is installed with CMake support
    # This will print a CMake error about processing arguments that can (currently) be ignored.
    ifneq (,$(SYSTEMC_EXISTS))
      FINDSC := $(shell mkdir -p build && cd build && cmake --find-package -DNAME=SystemCLanguage -DCMAKE_USE_PTHREADS_INIT=ON -DCOMPILER_ID=GNU -DLANGUAGE=CXX -DMODE=EXIST -DThreads_FOUND=ON)
      ifneq (,$(findstring SystemCLanguage found,$(FINDSC)))
        SYSTEMC_SET := true
      endif
    endif

    ifeq ($(SYSTEMC_SET), true)
      TARGET := run
    else
      TARGET := nosc
    endif
  endif
endif

default: $(TARGET)

run:
	@echo
	@echo "-- Verilator CMake SystemC tracing example"

	@echo
	@echo "-- VERILATE ----------------"
	mkdir -p build && cd build && cmake ..

	@echo
	@echo "-- BUILD -------------------"
	cmake --build build -j

	@echo
	@echo "-- RUN ---------------------"
	@mkdir -p logs
	build/example +trace_vcd

	@echo
	@echo "-- COVERAGE ----------------"
	$(VERILATOR_COVERAGE) --annotate logs/annotated logs/coverage.dat

	@echo
	@echo "-- DONE --------------------"
	@echo "To see waveforms, open vlt_dump.vcd in a waveform viewer"
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

nosc:
	@echo
	@echo "%Skip: CMake could not find SystemC."
	@echo "% Make sure that either:"
	@echo "% - The environment variables SYSTEMC_INCLUDE and SYSTEMC_LIBDIR are exported."
	@echo "% - Or, the environment variable SYSTEMC_ROOT is exported."
	@echo "% - Or, The environment variable SYSTEMC is exported."
	@echo "% - Or, if the SystemC installation provides CMake support,"
	@echo "%   that its installation prefix is in CMAKE_PREFIX_PATH."
	@echo "% Also that the C++ standard of the SystemC library is the same as this example."
	@echo "% Please see the Verilator documentation's CMake section for more information."
	@echo
