// DESCRIPTION: Verilator:
//  Test an error where a shift amount was out of bounds and the compiler treats the
//  value as undefined (Issue #803)
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jeff Bush.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    struct packed {
	logic flag;
	logic [130:0] data;
    } foo[1];

    integer cyc=0;

    // Test loop
    always @ (posedge clk) begin
	cyc <= cyc + 1;
	foo[0].data <= 0;
	foo[0].flag <= !foo[0].flag;
	if (cyc==10) begin
	   if (foo[0].data != 0) begin
	   	$display("bad data value %x", foo[0].data);
		$stop;
	   end
	   $write("*-* All Finished *-*\n");
	   $finish;
	end
    end
endmodule
