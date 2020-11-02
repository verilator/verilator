// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Peter Monsson.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;
   wire [31:0] in = cyc;

   Test test (/*AUTOINST*/
              // Inputs
              .clk                      (clk),
              .in                       (in[31:0]));


   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

package lpcm_pkg;
  class lpcm_tr;
    int latency;
    int sample;

    function new();
      latency = 0;
      sample = 0;
    endfunction

    function string convert2string();
      return $sformatf("sample=0x%0h latency=%0d", sample, latency);
    endfunction
  endclass
endpackage

//internal error happens when lpcm_pkg is not imported
//import lpcm_pkg::*;

module Test (/*AUTOARG*/
   // Inputs
   clk, in
   );

   input clk;
   input [31:0] in;

   initial begin
      string s;
      lpcm_pkg::lpcm_tr tr; // internal error happens when lpcm_pkg is not imported
      tr = new();
      tr.sample = 1;
      tr.latency = 2;
      s = tr.convert2string();
      $display("hello %s", tr.convert2string());
      if (s != "sample=0x1 latency=2") $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
