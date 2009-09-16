// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module a;
   reg a;
   initial begin
      $unknown_sys_task_call_to_be_bbox("blah");
      a = $unknown_sys_func_call(23);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
