// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/);

   initial begin
      if (task_as_func(1'b0)) $stop;
   end

   task task_as_func;
      input ign;
   endtask

endmodule
