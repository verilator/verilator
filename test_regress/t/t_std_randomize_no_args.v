// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

module t_no_args;
    bit [7:0] addr;
    bit [15:0] data;
    bit [7:0] old_addr;
    bit [15:0] old_data;
    int success;
    bit valid;

    initial begin
        old_addr = addr;
        old_data = data;

        success = std::randomize();
        valid = (success == 1) && (addr == old_addr) && (data == old_data);
        if (!valid) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
