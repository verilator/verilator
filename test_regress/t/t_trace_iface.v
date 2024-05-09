// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface counter_if;
   logic       valid;
   logic [3:0] value;
   logic       reset;
   modport counter_mp (input reset, output valid, output value);
   modport core_mp (output reset, input valid, input value);
endinterface

interface counter_if2 (counter_if.counter_mp c_mp);
   task automatic reset();
      c_mp.valid = '0;
      c_mp.value = '0;
   endtask
   task automatic init();
      c_mp.valid = '0;
      c_mp.value = '1;
   endtask
endinterface

interface counter_if3 (counter_if.counter_mp c_mp);
   task automatic reset();
      c_mp.valid = '0;
      c_mp.value = '0;
   endtask
   task automatic init();
      c_mp.valid = '1;
      c_mp.value = 4'ha;
   endtask
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   counter_if c5_data();
   counter_if c6_data();

   counter_if2 cif2(c5_data.counter_mp);
   counter_if3 cif3(c6_data.counter_mp);

   initial begin
      cif2.reset();
      cif3.reset();
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc<2) begin
         if (c5_data.valid != '0) $stop;
         if (c5_data.value != '0) $stop;
         if (c6_data.valid != '0) $stop;
         if (c6_data.value != '0) $stop;
      end
      if (cyc==2) begin
         cif2.init();
         cif3.init();
      end
      if (cyc==20) begin
         if (c5_data.valid != '0) $stop;
         if (c5_data.value != '1) $stop;
         if (c6_data.valid != '1) $stop;
         if (c6_data.value != 10) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
