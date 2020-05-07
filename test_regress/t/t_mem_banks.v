// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   reg [5:0] 	addr;

   parameter BANKS = 6;
   parameter ROWS = 8;

   wire [2:0]	bank;
   wire [2:0]	row;

   integer 	a;
   integer 	used[BANKS][ROWS];

   // Test loop
   initial begin
      for (a = 0; a < BANKS*ROWS; ++a) begin
	 addr[5:0] = a[5:0];
	 hash (addr, bank, row);
	 used [bank][row] ++;
	 if (used [bank][row] > 1) begin
	    $write ("Error: Hash failed addr=%x bank=%x row=%x\n", addr, bank, row);
	 end
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

   task hash (input [5:0] addr,
	      output [2:0] bank,
	      output [2:0] row);

      reg [1:0] third;
      reg [1:0] fourth;

      third = {addr[5], addr[4]};
      fourth = {addr[3] ^ addr[1],
		addr[2] ^ addr[0]};

      case (third)
	2'h0:
	  case (fourth)
	    2'h0: begin bank = 3'h0; row = {1'h0, addr[1:0]}; end
	    2'h1: begin bank = 3'h1; row = {1'h0, addr[1:0]}; end
	    2'h2: begin bank = 3'h2; row = {1'h0, addr[1:0]}; end
	    2'h3: begin bank = 3'h3; row = {1'h0, addr[1:0]}; end
	  endcase

	2'h1:
	  case (fourth)
	    2'h0: begin bank = 3'h0; row = {1'h1, addr[1:0]}; end
	    2'h1: begin bank = 3'h1; row = {1'h1, addr[1:0]}; end
	    2'h2: begin bank = 3'h4; row = {1'h0, addr[1:0]}; end
	    2'h3: begin bank = 3'h5; row = {1'h0, addr[1:0]}; end
	  endcase

	2'h2:
	  case (fourth)
	    2'h0: begin bank = 3'h2; row = {1'h1, addr[1:0]}; end
	    2'h1: begin bank = 3'h3; row = {1'h1, addr[1:0]}; end
	    2'h2: begin bank = 3'h4; row = {1'h1, addr[1:0]}; end
	    2'h3: begin bank = 3'h5; row = {1'h1, addr[1:0]}; end
	  endcase

	2'h3: $stop;
      endcase
   endtask
endmodule
