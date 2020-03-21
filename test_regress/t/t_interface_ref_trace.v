// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// Test for trace file interface aliasing

typedef struct packed {
   integer     val100;
   integer     val200;
} struct_t;

interface ifc (input logic clk,
               input integer cyc);
   integer 		     value;
   struct_t the_struct;
endinterface

module t (/*AUTOARG*/
	  // Inputs
	  clk
	  );

   input clk;
   integer cyc=0;

   ifc intf_1(.*);
   ifc intf_2(.*);

   always @(*) begin
      intf_1.value = cyc + 1;
      intf_2.value = cyc + 2;
   end

   sub_struct s1 (.intf_for_struct(intf_1));
   sub_struct s2 (.intf_for_struct(intf_2));
   sub_check c1 (.intf_for_check(intf_1));
   sub_check c2 (.intf_for_check(intf_2));
   sub_all a (.intf_one(intf_1),
              .intf_two(intf_2));
   // Intentionally longer scope name
   sub_all abcdefghijklmnopqrstuvwxyz (.intf_one(intf_2),
              .intf_two(intf_1));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==20) begin
	 if (intf_1.value != 21) $stop;
	 if (intf_2.value != 22) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module sub_struct
  (
   ifc intf_for_struct
   );

   always @(*) begin
      intf_for_struct.the_struct.val100 = intf_for_struct.value + 100;
      intf_for_struct.the_struct.val200 = intf_for_struct.value + 200;
   end

endmodule

module sub_check
  (
   ifc intf_for_check
   );

`ifdef NO_INLINE_A
   //verilator no_inline_module
`endif

   always @(posedge intf_for_check.clk) begin
      if (intf_for_check.the_struct.val100 != intf_for_check.value + 100) $stop;
      if (intf_for_check.the_struct.val200 != intf_for_check.value + 200) $stop;
   end

endmodule

module sub_all
  (
   ifc intf_one,
   ifc intf_two
   );

`ifdef NO_INLINE_B
   //verilator no_inline_module
`endif

   ifc intf_in_sub_all (
			.clk(intf_one.clk),
			.cyc(intf_one.cyc)
			);
   assign intf_in_sub_all.value = intf_one.value + 1000;

   sub_check ac1 (.intf_for_check(intf_one));
   sub_check ac2 (.intf_for_check(intf_two));
   sub_struct as3 (.intf_for_struct(intf_in_sub_all));
   sub_check ac3 (.intf_for_check(intf_in_sub_all));

endmodule
