// DESCRIPTION: Verilator: System Verilog test of enumerated type methods
//
// This code exercises the various enumeration methods
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty.
// SPDX-License-Identifier: CC0-1.0

// Contributed 2012 by M W Lund, Atmel Corporation and Jeremy Bennett, Embecosm.



// **** Pin Identifiers ****
typedef enum int
{
 PINID_A0 = 32'd0,                    // MUST BE ZERO!
 // - Standard Ports -
           PINID_A1, PINID_A2, PINID_A3, PINID_A4, PINID_A5, PINID_A6, PINID_A7,
 PINID_B0, PINID_B1, PINID_B2, PINID_B3, PINID_B4, PINID_B5, PINID_B6, PINID_B7,
 PINID_C0, PINID_C1, PINID_C2, PINID_C3, PINID_C4, PINID_C5, PINID_C6, PINID_C7,
 PINID_D0, PINID_D1, PINID_D2, PINID_D3, PINID_D4, PINID_D5, PINID_D6, PINID_D7,
 PINID_E0, PINID_E1, PINID_E2, PINID_E3, PINID_E4, PINID_E5, PINID_E6, PINID_E7,
 PINID_F0, PINID_F1, PINID_F2, PINID_F3, PINID_F4, PINID_F5, PINID_F6, PINID_F7,
 PINID_G0, PINID_G1, PINID_G2, PINID_G3, PINID_G4, PINID_G5, PINID_G6, PINID_G7,
 PINID_H0, PINID_H1, PINID_H2, PINID_H3, PINID_H4, PINID_H5, PINID_H6, PINID_H7,
// PINID_I0, PINID_I1, PINID_I2, PINID_I3, PINID_I4, PINID_I5, PINID_I6, PINID_I7,-> DO NOT USE!!!! I == 1
 PINID_J0, PINID_J1, PINID_J2, PINID_J3, PINID_J4, PINID_J5, PINID_J6, PINID_J7,
 PINID_K0, PINID_K1, PINID_K2, PINID_K3, PINID_K4, PINID_K5, PINID_K6, PINID_K7,
 PINID_L0, PINID_L1, PINID_L2, PINID_L3, PINID_L4, PINID_L5, PINID_L6, PINID_L7,
 PINID_M0, PINID_M1, PINID_M2, PINID_M3, PINID_M4, PINID_M5, PINID_M6, PINID_M7,
 PINID_N0, PINID_N1, PINID_N2, PINID_N3, PINID_N4, PINID_N5, PINID_N6, PINID_N7,
// PINID_O0, PINID_O1, PINID_O2, PINID_O3, PINID_O4, PINID_O5, PINID_O6, PINID_O7,-> DO NOT USE!!!! O == 0
 PINID_P0, PINID_P1, PINID_P2, PINID_P3, PINID_P4, PINID_P5, PINID_P6, PINID_P7,
 PINID_Q0, PINID_Q1, PINID_Q2, PINID_Q3, PINID_Q4, PINID_Q5, PINID_Q6, PINID_Q7,
 PINID_R0, PINID_R1, PINID_R2, PINID_R3, PINID_R4, PINID_R5, PINID_R6, PINID_R7,
 // - AUX Port (Custom) -
 PINID_X0, PINID_X1, PINID_X2, PINID_X3, PINID_X4, PINID_X5, PINID_X6, PINID_X7,
 // - PDI Port -
 PINID_D2W_DAT, PINID_D2W_CLK,
 // - Power Pins -
 PINID_VDD0, PINID_VDD1, PINID_VDD2, PINID_VDD3,
 PINID_GND0, PINID_GND1, PINID_GND2, PINID_GND3,
 // - Maximum number of pins -
 PINID_MAX
 } t_pinid;


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire  a = clk;
   wire  b = 1'b0;
   reg   c;

   test test_i (/*AUTOINST*/
                // Inputs
                .clk                    (clk));

   // This is a compile time only test. Immediately finish
   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule


module test (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Use the enumeration size to initialize a dynamic array
   t_pinid  e;
   int   myarray1 [] = new [e.num];

   always @(posedge clk) begin

`ifdef TEST_VERBOSE
      $write ("Enumeration has %d members\n", e.num);
`endif

      e = e.first;

      forever begin
         myarray1[e] <= e.prev;

`ifdef TEST_VERBOSE
         $write ("myarray1[%d] (enum %s) = %d\n", e, e.name, myarray1[e]);
`endif

         if (e == e.last) begin
            break;
         end
         else begin
            e = e.next;
         end
      end
   end

endmodule
