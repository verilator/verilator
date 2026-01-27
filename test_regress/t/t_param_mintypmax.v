// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   parameter MTM = (1:2:3);

   sub sub ();
   //UNSUP sub #(.MTM(10:20:30)) sub20name ();
   //UNSUP sub #(.MTM(100:200)) sub200name ();
   //UNSUP sub #(10:20:30) sub20pos ();
   //UNSUP sub #(100:200) sub200pos ();

   initial begin
      if (MTM != 2) $stop;
      //UNSUP if (sub20pos.MTM != 20) $stop;
      //UNSUP if (sub200pos.MTM != 200) $stop;
      //UNSUP if (sub20name.MTM != 20) $stop;
      //UNSUP if (sub200name.MTM != 200) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module sub #(parameter MTM = (1:2:3)) ();
endmodule
