// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class X;
   typedef enum int {
        INITIAL, RUNNING, SUSPENDED, COMPLETING, DONE
   } state_t;

   static string state_names[state_t] = '{
        INITIAL:    "INITIAL",
        RUNNING:    "RUNNING",
        SUSPENDED:  "SUSPENDED",
        COMPLETING: "COMPLETING",
        DONE:       "DONE"
   };
   protected state_t state;

   function new();
      this.state = INITIAL;
      `checks(state_names[this.state], "INITIAL");
      this.state = RUNNING;
      `checks(state_names[this.state], "RUNNING");
   endfunction

endclass

module t;/*AUTOARG*/


initial begin
   X x = new;
   $finish;
end



endmodule
