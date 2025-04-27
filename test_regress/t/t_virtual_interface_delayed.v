// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

interface Ifc;
   bit [7:0] rdata;
endinterface

class drv_c;
   virtual Ifc vif;

   virtual task run();
      #100;
      `checkh(vif.rdata, 8'haa);
      #100;
      `checkh(vif.rdata, 8'haa);
      #100;
   endtask
endclass

module dut (output wire [7:0] rd_val);
   assign rd_val = 8'haa;
endmodule

module m;
   drv_c d_0;

   Ifc u_Ifc ();
   dut u_dut (.rd_val (u_Ifc.rdata));

   initial begin
      d_0 = new();
      d_0.vif = u_Ifc;
      //u_Ifc.rdata = 10;
      d_0.run();
      $write("*-* All Finished *-*\n");
      $finish(2);
   end
endmodule
