// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (got), (exp)); `stop; end while(0)

module t;

  function void allfin;
    $write("*-* All Finished *-*\n");
  endfunction

  task done;
    $finish;
  endtask

  logic [16:0] clearBit_i;
  int          clearBit_idx;
  logic [16:0] clearBit_o;
  function automatic logic [16:0] clearBit(logic [16:0] i, int idx);
    i[idx] = 1'b0;
    return i;
  endfunction
  always_comb begin
    clearBit_o = clearBit(clearBit_i, clearBit_idx);
    `check(clearBit_o, (clearBit_i & ~(17'd1 << clearBit_idx)));
  end

  logic [2:0]  lut_idx;
  logic [4:0]  lut_o;
  localparam logic [4:0] LUT [7:0] = '{5'd0, 5'd1, 5'd2, 5'd3, 5'd4, 5'd5, 5'd6, 5'd7};
  function automatic logic [4:0] lut(logic [2:0] idx);
    return LUT[idx];
  endfunction
  always_comb begin
    lut_o = lut(lut_idx);
    `check(lut_o, 5'd7 - 5'(lut_idx));
  end

  initial begin
    #1;
    clearBit_i = 17'h1ff;
    for (int i = 0; i <= 16; ++i) begin
      clearBit_idx = i;
      #1;
    end

    #1;
    for (int i = 0; i < 16; ++i) begin
      lut_idx = 3'(i);
      #1;
    end

    #1;
    allfin();
    done();
  end

endmodule
