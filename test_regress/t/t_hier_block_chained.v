// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// Based on tests emitted by t_gate_tree.py

module t (clk);
  input clk;

  logic reset;

   reg [255:0] v2_0;
   reg [255:0] v1_0;
   reg [255:0] v1_1;
   reg [255:0] v1_2;
   reg [255:0] v1_3;
   reg [255:0] v1_4;
   reg [255:0] v1_5;
   reg [255:0] v1_6;
   reg [255:0] v1_7;
   reg [255:0] dummy;

   Calculate calc0(.clk(clk), .reset(reset), .v1_0(v1_0), .v1_1(dummy), .v1_2(dummy), .v1_3(dummy), .v1_4(dummy), .v1_5(dummy), .v1_6(dummy), .v1_7(dummy));
   Calculate calc1(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(v1_1), .v1_2(dummy), .v1_3(dummy), .v1_4(dummy), .v1_5(dummy), .v1_6(dummy), .v1_7(dummy));
   Calculate calc2(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(dummy), .v1_2(v1_2), .v1_3(dummy), .v1_4(dummy), .v1_5(dummy), .v1_6(dummy), .v1_7(dummy));
   Calculate calc3(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(dummy), .v1_2(dummy), .v1_3(v1_3), .v1_4(dummy), .v1_5(dummy), .v1_6(dummy), .v1_7(dummy));
   Calculate calc4(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(dummy), .v1_2(dummy), .v1_3(dummy), .v1_4(v1_4), .v1_5(dummy), .v1_6(dummy), .v1_7(dummy));
   Calculate calc5(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(dummy), .v1_2(dummy), .v1_3(dummy), .v1_4(dummy), .v1_5(v1_5), .v1_6(dummy), .v1_7(dummy));
   Calculate calc6(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(dummy), .v1_2(dummy), .v1_3(dummy), .v1_4(dummy), .v1_5(dummy), .v1_6(v1_6), .v1_7(dummy));
   Calculate calc7(.clk(clk), .reset(reset), .v1_0(dummy), .v1_1(dummy), .v1_2(dummy), .v1_3(dummy), .v1_4(dummy), .v1_5(dummy), .v1_6(dummy), .v1_7(v1_7));
   always @ (posedge clk) v2_0 <= v1_0 + v1_1 + v1_2 + v1_3 + v1_4 + v1_5 + v1_6 + v1_7;
   Check chk(.clk(clk), .reset(reset), .v2_0(v2_0));
endmodule

module Check(input clk, output logic reset, input reg [255:0] v2_0);
  integer cyc=0;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
         $write("[%0t] rst=%0x  v0_0=%0x  v1_0=%0x  result=%0x\n", $time, reset, v0_0, v1_0, v2_0);
`endif
      if (cyc==0) begin
         reset <= 1;
      end
      else if (cyc==10) begin
         reset <= 0;
      end
`ifndef SIM_CYCLES
 `define SIM_CYCLES 99
`endif
      else if (cyc==`SIM_CYCLES) begin
         if (v2_0 != 256'd2017) $stop;
         $write("VARS=64 WIDTH=256 WORKINGSET=2KB\n");
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Calculate(input clk,
   input reset,
   output reg [255:0] v1_0,
   output reg [255:0] v1_1,
   output reg [255:0] v1_2,
   output reg [255:0] v1_3,
   output reg [255:0] v1_4,
   output reg [255:0] v1_5,
   output reg [255:0] v1_6,
   output reg [255:0] v1_7
   );
   reg [255:0] v0_0;
   reg [255:0] v0_1;
   reg [255:0] v0_2;
   reg [255:0] v0_3;
   reg [255:0] v0_4;
   reg [255:0] v0_5;
   reg [255:0] v0_6;
   reg [255:0] v0_7;
   reg [255:0] v0_8;
   reg [255:0] v0_9;
   reg [255:0] v0_10;
   reg [255:0] v0_11;
   reg [255:0] v0_12;
   reg [255:0] v0_13;
   reg [255:0] v0_14;
   reg [255:0] v0_15;
   reg [255:0] v0_16;
   reg [255:0] v0_17;
   reg [255:0] v0_18;
   reg [255:0] v0_19;
   reg [255:0] v0_20;
   reg [255:0] v0_21;
   reg [255:0] v0_22;
   reg [255:0] v0_23;
   reg [255:0] v0_24;
   reg [255:0] v0_25;
   reg [255:0] v0_26;
   reg [255:0] v0_27;
   reg [255:0] v0_28;
   reg [255:0] v0_29;
   reg [255:0] v0_30;
   reg [255:0] v0_31;
   reg [255:0] v0_32;
   reg [255:0] v0_33;
   reg [255:0] v0_34;
   reg [255:0] v0_35;
   reg [255:0] v0_36;
   reg [255:0] v0_37;
   reg [255:0] v0_38;
   reg [255:0] v0_39;
   reg [255:0] v0_40;
   reg [255:0] v0_41;
   reg [255:0] v0_42;
   reg [255:0] v0_43;
   reg [255:0] v0_44;
   reg [255:0] v0_45;
   reg [255:0] v0_46;
   reg [255:0] v0_47;
   reg [255:0] v0_48;
   reg [255:0] v0_49;
   reg [255:0] v0_50;
   reg [255:0] v0_51;
   reg [255:0] v0_52;
   reg [255:0] v0_53;
   reg [255:0] v0_54;
   reg [255:0] v0_55;
   reg [255:0] v0_56;
   reg [255:0] v0_57;
   reg [255:0] v0_58;
   reg [255:0] v0_59;
   reg [255:0] v0_60;
   reg [255:0] v0_61;
   reg [255:0] v0_62;
   reg [255:0] v0_63;

   always @ (posedge clk) v0_0 <= reset ? 256'd1 : v0_1;
   always @ (posedge clk) v0_1 <= reset ? 256'd1 : v0_2;
   always @ (posedge clk) v0_2 <= reset ? 256'd2 : v0_3;
   always @ (posedge clk) v0_3 <= reset ? 256'd3 : v0_4;
   always @ (posedge clk) v0_4 <= reset ? 256'd4 : v0_5;
   always @ (posedge clk) v0_5 <= reset ? 256'd5 : v0_6;
   always @ (posedge clk) v0_6 <= reset ? 256'd6 : v0_7;
   always @ (posedge clk) v0_7 <= reset ? 256'd7 : v0_0;
   always @ (posedge clk) v0_8 <= reset ? 256'd8 : v0_9;
   always @ (posedge clk) v0_9 <= reset ? 256'd9 : v0_10;
   always @ (posedge clk) v0_10 <= reset ? 256'd10 : v0_11;
   always @ (posedge clk) v0_11 <= reset ? 256'd11 : v0_12;
   always @ (posedge clk) v0_12 <= reset ? 256'd12 : v0_13;
   always @ (posedge clk) v0_13 <= reset ? 256'd13 : v0_14;
   always @ (posedge clk) v0_14 <= reset ? 256'd14 : v0_15;
   always @ (posedge clk) v0_15 <= reset ? 256'd15 : v0_8;
   always @ (posedge clk) v0_16 <= reset ? 256'd16 : v0_17;
   always @ (posedge clk) v0_17 <= reset ? 256'd17 : v0_18;
   always @ (posedge clk) v0_18 <= reset ? 256'd18 : v0_19;
   always @ (posedge clk) v0_19 <= reset ? 256'd19 : v0_20;
   always @ (posedge clk) v0_20 <= reset ? 256'd20 : v0_21;
   always @ (posedge clk) v0_21 <= reset ? 256'd21 : v0_22;
   always @ (posedge clk) v0_22 <= reset ? 256'd22 : v0_23;
   always @ (posedge clk) v0_23 <= reset ? 256'd23 : v0_16;
   always @ (posedge clk) v0_24 <= reset ? 256'd24 : v0_25;
   always @ (posedge clk) v0_25 <= reset ? 256'd25 : v0_26;
   always @ (posedge clk) v0_26 <= reset ? 256'd26 : v0_27;
   always @ (posedge clk) v0_27 <= reset ? 256'd27 : v0_28;
   always @ (posedge clk) v0_28 <= reset ? 256'd28 : v0_29;
   always @ (posedge clk) v0_29 <= reset ? 256'd29 : v0_30;
   always @ (posedge clk) v0_30 <= reset ? 256'd30 : v0_31;
   always @ (posedge clk) v0_31 <= reset ? 256'd31 : v0_24;
   always @ (posedge clk) v0_32 <= reset ? 256'd32 : v0_33;
   always @ (posedge clk) v0_33 <= reset ? 256'd33 : v0_34;
   always @ (posedge clk) v0_34 <= reset ? 256'd34 : v0_35;
   always @ (posedge clk) v0_35 <= reset ? 256'd35 : v0_36;
   always @ (posedge clk) v0_36 <= reset ? 256'd36 : v0_37;
   always @ (posedge clk) v0_37 <= reset ? 256'd37 : v0_38;
   always @ (posedge clk) v0_38 <= reset ? 256'd38 : v0_39;
   always @ (posedge clk) v0_39 <= reset ? 256'd39 : v0_32;
   always @ (posedge clk) v0_40 <= reset ? 256'd40 : v0_41;
   always @ (posedge clk) v0_41 <= reset ? 256'd41 : v0_42;
   always @ (posedge clk) v0_42 <= reset ? 256'd42 : v0_43;
   always @ (posedge clk) v0_43 <= reset ? 256'd43 : v0_44;
   always @ (posedge clk) v0_44 <= reset ? 256'd44 : v0_45;
   always @ (posedge clk) v0_45 <= reset ? 256'd45 : v0_46;
   always @ (posedge clk) v0_46 <= reset ? 256'd46 : v0_47;
   always @ (posedge clk) v0_47 <= reset ? 256'd47 : v0_40;
   always @ (posedge clk) v0_48 <= reset ? 256'd48 : v0_49;
   always @ (posedge clk) v0_49 <= reset ? 256'd49 : v0_50;
   always @ (posedge clk) v0_50 <= reset ? 256'd50 : v0_51;
   always @ (posedge clk) v0_51 <= reset ? 256'd51 : v0_52;
   always @ (posedge clk) v0_52 <= reset ? 256'd52 : v0_53;
   always @ (posedge clk) v0_53 <= reset ? 256'd53 : v0_54;
   always @ (posedge clk) v0_54 <= reset ? 256'd54 : v0_55;
   always @ (posedge clk) v0_55 <= reset ? 256'd55 : v0_48;
   always @ (posedge clk) v0_56 <= reset ? 256'd56 : v0_57;
   always @ (posedge clk) v0_57 <= reset ? 256'd57 : v0_58;
   always @ (posedge clk) v0_58 <= reset ? 256'd58 : v0_59;
   always @ (posedge clk) v0_59 <= reset ? 256'd59 : v0_60;
   always @ (posedge clk) v0_60 <= reset ? 256'd60 : v0_61;
   always @ (posedge clk) v0_61 <= reset ? 256'd61 : v0_62;
   always @ (posedge clk) v0_62 <= reset ? 256'd62 : v0_63;
   always @ (posedge clk) v0_63 <= reset ? 256'd63 : v0_56;

   always @ (posedge clk) v1_0 <= v0_0 + v0_1 + v0_2 + v0_3 + v0_4 + v0_5 + v0_6 + v0_7;
   always @ (posedge clk) v1_1 <= v0_8 + v0_9 + v0_10 + v0_11 + v0_12 + v0_13 + v0_14 + v0_15;
   always @ (posedge clk) v1_2 <= v0_16 + v0_17 + v0_18 + v0_19 + v0_20 + v0_21 + v0_22 + v0_23;
   always @ (posedge clk) v1_3 <= v0_24 + v0_25 + v0_26 + v0_27 + v0_28 + v0_29 + v0_30 + v0_31;
   always @ (posedge clk) v1_4 <= v0_32 + v0_33 + v0_34 + v0_35 + v0_36 + v0_37 + v0_38 + v0_39;
   always @ (posedge clk) v1_5 <= v0_40 + v0_41 + v0_42 + v0_43 + v0_44 + v0_45 + v0_46 + v0_47;
   always @ (posedge clk) v1_6 <= v0_48 + v0_49 + v0_50 + v0_51 + v0_52 + v0_53 + v0_54 + v0_55;
   always @ (posedge clk) v1_7 <= v0_56 + v0_57 + v0_58 + v0_59 + v0_60 + v0_61 + v0_62 + v0_63;
endmodule
