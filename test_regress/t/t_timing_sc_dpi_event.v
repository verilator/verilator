// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 ViraSemi Inc.
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps

module t;

   event hit;

   time  woke_at = 0;

   export "DPI-C" function sv_trigger;

   // Called from SystemC at 10ns. Triggers an event a process is already waiting on.
   function automatic void sv_trigger();
      ->hit;
   endfunction

   initial begin
      @(hit);
      woke_at = $time;
   end

   initial begin
      #50;
      if (woke_at != 10) begin
         $write("%%Error: the waiting process was released at %0t, expected 10ns\n", woke_at);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
