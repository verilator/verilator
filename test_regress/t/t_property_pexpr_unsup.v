// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int   a;
   int   b;
   int   c;
   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
   end

   // NOTE this grammar hasn't been checked with other simulators,
   // is here just to avoid uncovered code lines in the grammar.
   property p_strong;
      strong(a);
   endproperty

   property p_weak;
      weak(a);
   endproperty

   property p_until;
      a until b;
   endproperty

   property p_suntil;
      a s_until b;
   endproperty

   property p_untilwith;
      a until_with b;
   endproperty

   property p_suntilwith;
      a s_until_with b;
   endproperty

   property p_implies;
      a implies b;
   endproperty

   property p_poundminuspound1;
      a #-# b;
   endproperty

   property p_poundeqpound;
      a #=# b;
   endproperty

   property p_nexttime;
      nexttime a;
   endproperty

   property p_nexttime2;
      nexttime [2] a;
   endproperty

   property p_snexttime;
      s_nexttime a;
   endproperty

   property p_snexttime2;
      s_nexttime [2] a;
   endproperty

   property p_nexttime_always;
      nexttime always a;
   endproperty

   property p_nexttime_always2;
      nexttime [2] always a;
   endproperty

   property p_nexttime_eventually;
      nexttime eventually a;
   endproperty

   property p_nexttime_eventually2;
      nexttime [2] always a;
   endproperty

   property p_nexttime_seventually;
      nexttime s_eventually a;
   endproperty

   property p_nexttime_seventually2;
      nexttime s_eventually [2:$] always a;
   endproperty

   property p_accepton;
      accept_on (a) b;
   endproperty

   property p_syncaccepton;
      sync_accept_on (a) b;
   endproperty

   property p_rejecton;
      reject_on (a) b;
   endproperty

   property p_syncrejecton;
      sync_reject_on (a) b;
   endproperty

   property p_iff;
      a iff b;
   endproperty

   property p_arg_propery(property inprop);
      inprop;
   endproperty
   property p_arg_seqence(sequence inseq);
      inseq;
   endproperty

   property p_case_1;
      case (a) endcase
   endproperty
   property p_case_2;
      case (a) default: b; endcase
   endproperty
   property p_if;
      if (a) b
   endproperty
   property p_ifelse;
      if (a) b else c
   endproperty

   always @(posedge clk) begin
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
