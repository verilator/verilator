// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   real n0; initial n0 = 0.0;
   real n1; initial n1 = 1.0;
   real n2; initial n2 = 0.1;
   real n3; initial n3 = 1.2345e-15;
   real n4; initial n4 = 2.579e+15;
   reg [7:0] r8;  initial r8 = 3;

   initial begin
      // Display formatting
      $display("[%0t] e=%e e1=%1e e30=%3.0e e32=%3.2e", $time, n0,n0,n0,n0);
      $display("[%0t] f=%f f1=%1e f30=%3.0e f32=%3.2e", $time, n0,n0,n0,n0);
      $display("[%0t] g=%g g1=%1e g30=%3.0e g32=%3.2e", $time, n0,n0,n0,n0);
      $display;
      $display("[%0t] e=%e e1=%1e e30=%3.0e e32=%3.2e", $time, n1,n1,n1,n1);
      $display("[%0t] f=%f f1=%1e f30=%3.0e f32=%3.2e", $time, n1,n1,n1,n1);
      $display("[%0t] g=%g g1=%1e g30=%3.0e g32=%3.2e", $time, n1,n1,n1,n1);
      $display;
      $display("[%0t] e=%e e1=%1e e30=%3.0e e32=%3.2e", $time, n2,n2,n2,n2);
      $display("[%0t] f=%f f1=%1e f30=%3.0e f32=%3.2e", $time, n2,n2,n2,n2);
      $display("[%0t] g=%g g1=%1e g30=%3.0e g32=%3.2e", $time, n2,n2,n2,n2);
      $display;
      $display("[%0t] e=%e e1=%1e e30=%3.0e e32=%3.2e", $time, n3,n3,n3,n3);
      $display("[%0t] f=%f f1=%1e f30=%3.0e f32=%3.2e", $time, n3,n3,n3,n3);
      $display("[%0t] g=%g g1=%1e g30=%3.0e g32=%3.2e", $time, n3,n3,n3,n3);
      $display;
      $display("[%0t] e=%e e1=%1e e30=%3.0e e32=%3.2e", $time, n4,n4,n4,n4);
      $display("[%0t] f=%f f1=%1e f30=%3.0e f32=%3.2e", $time, n4,n4,n4,n4);
      $display("[%0t] g=%g g1=%1e g30=%3.0e g32=%3.2e", $time, n4,n4,n4,n4);
      $display;
      $display("r8=%d n1=%g n2=%g", r8, n1, n2);
      $display("n1=%g n2=%g r8=%d", n1, n2, r8);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
