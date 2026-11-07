// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Hudson River Trading LLC
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;

  function automatic int case_return(bit kind, bit cond);
    case (kind)
      0: return cond ? 11 : 12;  // CHECK_COVER(0,"top.t","case",2)
      1: return cond ? 21 : 22;  // CHECK_COVER(0,"top.t","case",2)
    endcase
  endfunction

  function automatic int if_return(bit kind);
    if (kind) return 1;  // CHECK_COVER(0,"top.t","if",2)
    else return 0;  // CHECK_COVER(-1,"top.t","else",2)
  endfunction

  function automatic int case_break(bit kind);
    int result = 0;
    for (int i = 0; i < 2; ++i) begin
      case (kind)
        0: ++result;  // CHECK_COVER(0,"top.t","case",4)
        default: break;  // CHECK_COVER(0,"top.t","case",2)
      endcase
    end
    return result;
  endfunction

  function automatic int case_continue(bit kind);
    int result = 0;
    for (int i = 0; i < 2; ++i) begin
      case (kind)
        1: continue;  // CHECK_COVER(0,"top.t","case",4)
        default: ++result;  // CHECK_COVER(0,"top.t","case",4)
      endcase
      ++result;
    end
    return result;
  endfunction

  function automatic int elsif_return(bit [1:0] kind);
    if (kind == 0) return 0;  // CHECK_COVER(0,"top.t","elsif",1)
    else if (kind == 1) return 1;  // CHECK_COVER(0,"top.t","if",1)
    else return 2;  // CHECK_COVER(-1,"top.t","else",2)
  endfunction

  function automatic int default_return(bit [1:0] kind);
    case (kind)
      0: return 0;  // CHECK_COVER(0,"top.t","case",1)
      default: return 1;  // CHECK_COVER(0,"top.t","case",3)
    endcase
  endfunction

  function automatic int loop_continue(bit kind);
    int result = 0;
    for (int i = 0; i < 2; ++i) begin
      if (kind) continue;  // CHECK_COVER(0,"top.t","if",4)
      ++result;
    end
    return result;
  endfunction

  function automatic int loop_return(bit kind);
    for (int i = 0; i < 2; ++i) begin
      if (kind) return i;  // CHECK_COVER(0,"top.t","if",2)
    end
    return 2;
  endfunction

  function automatic int loop_break(bit kind);
    int result = 0;
    for (int i = 0; i < 2; ++i) begin
      if (kind) break;  // CHECK_COVER(0,"top.t","if",2)
      ++result;
    end
    return result;
  endfunction

  always @(posedge clk) begin
    if (cyc < 4) begin
      `checkd(case_return(cyc[1], cyc[0]), (cyc[1] ? 20 : 10) + (cyc[0] ? 1 : 2));
      `checkd(case_break(cyc[0]), cyc[0] ? 0 : 2);
      `checkd(case_continue(cyc[0]), cyc[0] ? 0 : 4);
      `checkd(if_return(cyc[0]), int'(cyc[0]));
      `checkd(loop_return(cyc[0]), cyc[0] ? 0 : 2);
      `checkd(loop_break(cyc[0]), cyc[0] ? 0 : 2);
      `checkd(elsif_return(cyc[1:0]), cyc < 2 ? cyc : 2);
      `checkd(default_return(cyc[1:0]), cyc == 0 ? 0 : 1);
      `checkd(loop_continue(cyc[0]), cyc[0] ? 0 : 2);
      cyc <= cyc + 1;
    end
    else begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
