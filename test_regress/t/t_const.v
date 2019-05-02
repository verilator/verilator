// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t (/*AUTOARG*/);

   initial begin
      // verilator lint_off WIDTH
      if (32'hxxxxxxxx !== 'hx) $stop;
      if (32'hzzzzzzzz !== 'hz) $stop;
      if (32'h???????? !== 'h?) $stop;
      if (32'hxxxxxxxx !== 'dx) $stop;
      if (32'hzzzzzzzz !== 'dz) $stop;
      if (32'h???????? !== 'd?) $stop;
      // verilator lint_on WIDTH
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
