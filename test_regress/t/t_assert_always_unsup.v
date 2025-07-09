// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;
   int cyc = 0;
   logic val = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      val = ~val;
   end

   property p_alw;
      always [2:5] a;
   endproperty

   property p_s_alw;
      s_always [2:5] a;
   endproperty

   property p_ev;
      eventually [2:5] a;
   endproperty

   property p_ev2;
      eventually [2] a;
   endproperty

   property p_s_ev;
      s_eventually [2:5] a;
   endproperty

   property p_s_alw_ev;
      always s_eventually [2:5] a;
   endproperty

   property p_s_ev_alw;
      s_eventually always [2:5] a;
   endproperty

endmodule
