#!/usr/bin/env python3
# DESCRIPTION: Verilator: Test constant parameter slicing of unpacked arrays (issue #6257)

import vltest_bootstrap

# Use the Verilator scenario.  Other scenarios such as 'sc' (SystemC) are not needed here.
test.scenarios('vlt')

# Compile the Verilog source (t_param_slice.v is detected automatically)
test.compile(verilator_flags2=['--exe','--main','--timing'])

# Run the compiled simulation
test.execute()

# Mark the test as passed if no errors occurred and the "*-* All Finished *-*"
# marker is printed by the Verilog code.
test.passes()
