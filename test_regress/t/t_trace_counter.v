// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (
	 // Outputs
	 state,
	 // Inputs
	 clk);

    input clk;
    reg rst;
    output [7:0] state;

	 counter c0 (
        .clk (clk),
        .rst (rst),
	     .out (state));

    int cyc;

    always @ (posedge clk) begin
        cyc <= cyc + 1;
        if (cyc == 0) begin
            rst <= 1;
        end
        else if (cyc == 10) begin
            rst <= 0;
        end
        else if (cyc == 11) begin
            rst <= 1;
        end
        else if (cyc == 99) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule

module counter (
	 input clk,
	 input rst,
	 output reg[7:0] out);

	 always @ (posedge clk) begin
		  if (!rst)
			   out <= 0;
		  else
			   out <= out + 1;
	 end
endmodule
