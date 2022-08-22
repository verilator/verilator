// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  logic[3:0] val[3];
  logic[1:0] idx1 = 0;
  logic[1:0] idx2 = 0;
  logic[0:0] idx3 = 0;
  event e;

  always @val[0] $write("val[0]=%0d val[1]=%0d val[2]=%0d\n", val[0], val[1], val[2]);

  assign #10 {val[1], val[2]} = {val[0], 4'hf-val[0]};

  always #10 begin  // always so we can use NBA
    val[0] = 1;
    #10 val[0] = 2;
    fork #5 val[0] = 3; join_none
    val[0] = #10 val[0] + 2;
    val[idx1] <= #10 val[idx1] + 2;
    fork begin #5
        val[0] = 5;
        idx1 = 2;
        idx2 = 3;
        idx3 = 1;
        #40 ->e;
    end join_none
    val[idx1][idx2[idx3+:2]] = #20 1;
    @e val[0] = 8;
    fork begin
        #1 val[0] = 9;
        #2 ->e;
    end join_none
    val[0] = @e val[0] + 2;
    val[0] <= @e val[0] + 2;
    fork begin
        #1 val[0] = 11;
    end join_none
    #2 ->e;
    idx1 = 0;
    idx2 = 0;
    idx3 = 0;
    fork begin #2
        idx1 = 2;
        idx2 = 3;
        idx3 = 1;
    end join_none
    #1 val[idx1[idx3+:2]][idx2] <= @e 1;
    #1 ->e;
    #1 $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
