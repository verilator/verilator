// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic       use_AnB;

   logic [1:0] active_command  [8:0];
   logic [1:0] command_A       [8:0];
   logic [1:0] command_B       [8:0];

   logic [1:0] active_command2 [8:0];
   logic [1:0] command_A2      [7:0];
   logic [1:0] command_B2      [8:0];

   logic [1:0] active_command3 [1:0][2:0][3:0];
   logic [1:0] command_A3      [1:0][2:0][3:0];
   logic [1:0] command_B3      [1:0][2:0][3:0];

   logic [1:0] active_command4 [8:0];
   logic [1:0] command_A4      [7:0];

   logic [1:0] active_command5 [8:0];
   logic [1:0] command_A5      [7:0];

   // Single dimension assign
   assign active_command[3:0] = (use_AnB) ? command_A[7:0] : command_B[7:0];
   // Assignment of entire arrays
   assign active_command2 = (use_AnB) ? command_A2 : command_B2;
   // Multi-dimension assign
   assign active_command3[1:0][2:0][3:0] = (use_AnB) ?  command_A3[1:0][2:0][3:0] : command_B3[1:0][1:0][3:0];

   // Supported: Delayed assigment with RHS Var == LHS Var
   logic [7:0] arrd [7:0];
   always_ff @(posedge clk) arrd[7:4] <= arrd[3:0];

   // Unsupported: Non-delayed assigment with RHS Var == LHS Var
   logic [7:0] arr [7:0];
   assign arr[7:4] = arr[3:0];

   // Delayed assign
   always @(posedge clk) begin
      active_command4[7:0] <= command_A4[8:0];
   end

   // Combinational assign
   always_comb begin
      active_command5[8:0] = command_A5[7:0];
   end

endmodule : t
