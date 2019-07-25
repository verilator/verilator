#!/usr/bin/env python3

# DESCRIPTION: Verilator: Verilog example python module
#
# This file ONLY is placed into the Public Domain, for any use,
# without warranty, 2017 by Wilson Snyder.
#======================================================================

import os
import sys
# Search the build directory
sys.path.append(os.path.join(os.path.dirname(os.path.realpath(__file__)), "obj_dir"))

import Vtop


def main():
    # See a similar example walkthrough in the verilator manpage.
    Vtop.Verilated.parse_arguments(sys.argv[1:])

    # This is intended to be a minimal example.  Before copying this to start a
    # real project, it is better to start with a more complete example,
    # e.g. examples/c_tracing.

    # Construct the Verilated model
    top = Vtop.Vtop()

    # Simulate until $finish
    while not Vtop.Verilated.finished:
        top.eval()

    # Final model cleanup
    top.final()

    # Destroy model
    del top

    # Fin
    sys.exit(0);


if __name__ == "__main__":
    main()
