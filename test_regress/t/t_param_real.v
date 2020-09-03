// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork
// SPDX-License-Identifier: CC0-1.0

module mod #(
    parameter real HZ = 0
);
   //verilator no_inline_module
   initial begin
      if ((HZ-$floor(HZ)) - 0.45 > 0.01) $stop;
      if ((HZ-$floor(HZ)) - 0.45 < -0.01) $stop;
   end
endmodule

module t();
   mod #(.HZ(123.45)) mod1();
   mod #(.HZ(24.45)) mod2();

   initial begin
      if (mod1.HZ != 123.45) $stop;
      if (mod2.HZ != 24.45) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
