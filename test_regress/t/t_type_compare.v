// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module Sub #(parameter type T = type(logic[11:0]));
endmodule

module t;

   int case_ok;

   Sub #(.T(int)) sub();

   typedef logic [12:0] logic12_t;

   // Generate if
   if (type(logic[12:0]) !== type(logic[12:0])) initial $stop;
   if (type(logic[12:0]) != type(logic12_t)) initial $stop;
   if (type(logic[12:0]) !== type(logic12_t)) initial $stop;
   if (type(logic[22:0]) == type(logic12_t)) initial $stop;
   if (type(logic[22:0]) === type(logic12_t)) initial $stop;
   // Generate case
   case (type(real))
     type(int): initial $stop;
     type(real): ;
     default: initial $stop;
   endcase

   initial begin
      if (type(real) == type(logic[12:0])) $stop;
      if (type(real) === type(logic[12:0])) $stop;
      if (type(real) != type(real)) $stop;
      if (type(real) !== type(real)) $stop;
      if (type(logic[12:0]) !== type(logic[12:0])) $stop;
      if (type(logic[12:0]) != type(logic12_t)) $stop;
      if (type(logic[12:0]) !== type(logic12_t)) $stop;
      if (type(logic[22:0]) == type(logic12_t)) $stop;
      if (type(logic[22:0]) === type(logic12_t)) $stop;

      // Item selected
      case (type(real))
        type(real): case_ok = 1;
        type(int): $stop;
        type(chandle): $stop;
        default: $stop;
      endcase
      if (case_ok != 1) $stop;

      // Default selected
      case (type(real))
        type(int): $stop;
        default: case_ok = 2;
      endcase
      if (case_ok != 2) $stop;

      // No body selected
      case (type(real))
        type(int): $stop;
      endcase
      if (case_ok != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
