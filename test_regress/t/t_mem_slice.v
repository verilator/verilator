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
   logic [1:0] active_command [8:0];
   logic [1:0] command_A      [8:0];
   logic [1:0] command_B      [8:0];

   logic [1:0] active_command2 [8:0];
   logic [1:0] command_A2      [8:0];
   logic [1:0] command_B2      [8:0];

   logic [1:0] active_command3 [1:0][2:0][3:0];
   logic [1:0] command_A3      [1:0][2:0][3:0];
   logic [1:0] command_B3      [1:0][2:0][3:0];

   logic      [2:0] use_A4nB4;
   logic [8:0][1:0] active_command4;
   logic [8:0][1:0] command_A4;
   logic [8:0][1:0] command_B4;

   logic [8:0] pipe1	      [7:0];
   logic [8:0] pipe1_input;

   integer cyc;

   assign active_command[8:0] = (use_AnB) ? command_A[8:0] : command_B[8:0];
   assign active_command2 = (use_AnB) ? command_A2 : command_B2;
   // Illegal to have [1:0][x:y] here - IEEE only allows single dimension slicing
   assign active_command3[1:0] = (use_AnB) ?  command_A3[1:0] : command_B3[1:0];

   // Check we can cope with things other than packed arrays
   assign active_command4 = (use_A4nB4[0]) ?  command_A4 : command_B4;

   always @ (posedge clk) begin
      pipe1_input <= pipe1_input + 1;
      pipe1[0]    <= pipe1_input;
      pipe1[7:1]  <= pipe1[6:0];
   end

   logic [3:0][13:0] iq_read_data [15:0];
   logic [3:0][13:0] iq_data;
   logic [3:0]       sel;

   assign iq_data = iq_read_data[sel];

   always @ (posedge clk) begin
      sel = sel + 1;
   end

   initial begin
      cyc = 0;
      use_AnB = 0;
      for (int i = 0; i < 7; ++i) begin
	 command_A[i] = 2'b00;
	 command_B[i] = 2'b11;
	 command_A2[i] = 2'b00;
	 command_B2[i] = 2'b11;
	 pipe1_input = 9'b0;
      end
      for (int i = 0; i < 2; ++i) begin
	 for (int j = 0; j < 3; ++j) begin
	    for (int k = 0; k < 4; ++k) begin
	       command_A3[i][j][k] = 2'b00;
	       command_B3[i][j][k] = 2'b11;
	    end
	 end
      end
   end

   always @ (posedge clk) begin
      use_AnB <= ~use_AnB;
      cyc <= cyc + 1;
      if (use_AnB) begin
	 if (active_command[3] != 2'b00) begin
	    $stop;
	 end
	 if (active_command2[3] != 2'b00) begin
	    $stop;
	 end
	 if (active_command3[0][1][2] != 2'b00) begin
	    $stop;
	 end
      end
      if (!use_AnB) begin
	 if (active_command[3] != 2'b11) begin
	    $stop;
	 end
	 if (active_command2[3] != 2'b11) begin
	    $stop;
	 end
      end
   end

   logic [8:0] last_pipe;
   always @(posedge clk) begin
      if (cyc < 3) begin
	 last_pipe <= pipe1[0];
      end
      else begin
	 if (last_pipe + 1 != pipe1[0]) begin
	    $stop;
	 end
	 else begin
	    last_pipe <= pipe1[0];
	 end
      end
      if (cyc > 10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule : t
