// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

function integer get_baz(input integer bar);
   get_baz = bar;
   $fatal(2, "boom");
endfunction

module foo #(parameter BAR = 0);
   localparam integer BAZ = get_baz(BAR);
endmodule

module foo2 #(parameter QUX = 0);
   genvar x;
   generate
      for (x = 0; x < 2; x++) begin: foo2_loop
         foo #(.BAR (QUX + x)) foo_in_foo2_inst();
      end
   endgenerate
endmodule

module t;
   genvar i, j;
   generate
      for (i = 0; i < 2; i++) begin: genloop
         foo #(.BAR (i)) foo_inst();
      end
      for (i = 2; i < 4; i++) begin: gen_l1
         for (j = 0; j < 2; j++) begin: gen_l2
            foo #(.BAR (i + j*2)) foo_inst2();
         end
      end
      if (1 == 1) begin: cond_true
         foo #(.BAR (6)) foo_inst3();
      end
      if (1 == 1) begin // unnamed
         foo #(.BAR (7)) foo_inst4();
      end
      for (i = 8; i < 12; i = i + 2) begin: nested_loop
         foo2 #(.QUX (i)) foo2_inst();
      end
   endgenerate
endmodule
