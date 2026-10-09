// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [6:0] data;
  logic [6:0] result;
  logic [2:0] index;
  logic match_zero;
  logic match_one;
  logic match_x;
  logic match_z;
  logic match_cond_plain;
  logic match_cond_x;
  logic match_cond_z;
  logic match_cond_inside;
  logic match_cond_range;
  logic match_range_bounds;

  always_comb begin
    // The retained loop makes the select's bounds check a conditional case item.
    for (int i = 0; i < 7; i++) begin
      unique case (1'b1)
        // verilator lint_off CASEWITHX
        data[i]: result[i] = 1'b1;
        // verilator lint_on CASEWITHX
        default: result[i] = 1'b0;
      endcase
    end
    case (1'b0)
      // verilator lint_off CASEWITHX
      data[index]: match_zero = 1'b1;
      // verilator lint_on CASEWITHX
      default: match_zero = 1'b0;
    endcase
    case (1'b1)
      // verilator lint_off CASEWITHX
      data[index]: match_one = 1'b1;
      // verilator lint_on CASEWITHX
      default: match_one = 1'b0;
    endcase
    // verilator lint_off CASEX
    casex (1'b1)
    // verilator lint_on CASEX
      data[index]: match_x = 1'b1;
      default: match_x = 1'b0;
    endcase
    casez (1'b1)
      // verilator lint_off CASEWITHX
      data[index]: match_z = 1'b1;
      // verilator lint_on CASEWITHX
      default: match_z = 1'b0;
    endcase
    case (2'b10)
      // verilator lint_off CASEWITHX
      (index == 7 ? 2'b?0 : index == 0 ? 2'bx0 : data[1:0]): match_cond_plain = 1'b1;
      // verilator lint_on CASEWITHX
      default: match_cond_plain = 1'b0;
    endcase
    // verilator lint_off CASEX
    casex (2'b10)
    // verilator lint_on CASEX
      (index == 7 ? 2'b?0 : index == 0 ? 2'bx0 : data[1:0]): match_cond_x = 1'b1;
      default: match_cond_x = 1'b0;
    endcase
    casez (2'b10)
      // verilator lint_off CASEWITHX
      (index == 7 ? 2'b?0 : index == 0 ? 2'bx0 : data[1:0]): match_cond_z = 1'b1;
      // verilator lint_on CASEWITHX
      default: match_cond_z = 1'b0;
    endcase
    case (2'b10) inside
      // verilator lint_off CASEWITHX
      (index == 7 ? 2'b?0 : index == 0 ? 2'bx0 : data[1:0]): match_cond_inside = 1'b1;
      // verilator lint_on CASEWITHX
      default: match_cond_inside = 1'b0;
    endcase
    case (1'b1)
      (index[0] ? (data[2:0] inside {[3'd1:3'd3]}) : data[4]): match_cond_range = 1'b1;
      default: match_cond_range = 1'b0;
    endcase
    case (data[2:0]) inside
      [(index[0] ? 3'd1 : 3'd4):(index[0] ? 3'd3 : 3'd5)]: match_range_bounds = 1'b1;
      default: match_range_bounds = 1'b0;
    endcase
  end

  initial begin
    for (int sample = 0; sample < 128; sample++) begin
      data = 7'(sample);
      for (int j = 0; j < 8; j++) begin
        index = 3'(j);
        #1;
        `checkh(result, data);
        if (j < 7) begin
          `checkh(match_zero, !data[j]);
          `checkh(match_one, data[j]);
          `checkh(match_x, data[j]);
          `checkh(match_z, data[j]);
        end else begin
          `checkh(match_zero, 1'b0);
          `checkh(match_one, 1'b0);
          `checkh(match_x, 1'b1);
          `checkh(match_z, 1'b0);
        end
        `checkh(match_cond_plain, j != 7 && j != 0 && data[1:0] == 2'b10);
        `checkh(match_cond_x, j == 7 || j == 0 || data[1:0] == 2'b10);
        `checkh(match_cond_z, j == 7 || (j != 0 && data[1:0] == 2'b10));
        `checkh(match_cond_inside, j == 7 || j == 0 || data[1:0] == 2'b10);
        `checkh(match_cond_range, j[0] ? (data[2:0] >= 1 && data[2:0] <= 3) : data[4]);
        `checkh(match_range_bounds, j[0] ? (data[2:0] >= 1 && data[2:0] <= 3)
                                       : (data[2:0] >= 4 && data[2:0] <= 5));
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
