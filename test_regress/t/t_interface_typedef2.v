// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface common_intf #(
    int ADDR_W,
    DATA_W
);
  typedef struct packed {

    logic [ADDR_W-1:0] cntr_idx;
    logic [DATA_W-1:0] cntr_val;

  } stage_t;

  stage_t bus;

endinterface

module mod1 (
    common_intf p1
);
  typedef p1.stage_t stage_t;  // "imports" type into module
  stage_t local_bus;

  initial begin
    $display("%m mod1: idx bits %0d, val bits %0d", $bits(p1.bus.cntr_idx), $bits(p1.bus.cntr_val));
  end
endmodule

module mod2 (
    common_intf p1,
    p2
);
  typedef p1.stage_t stage1_t;  // "imports" type into module
  stage1_t local_bus1;

  typedef p2.stage_t stage2_t;  // "imports" type into module
  stage2_t local_bus2;

  initial begin
    $display("%m-1 mod2: idx bits %0d, val bits %0d", $bits(p1.bus.cntr_idx), $bits(p1.bus.cntr_val));
    $display("%m-2 mod2: idx bits %0d, val bits %0d", $bits(p2.bus.cntr_idx), $bits(p2.bus.cntr_val));
    $display("%m mod2: params p1 ADDR_W %0d DATA_W %0d", p1.ADDR_W, p1.DATA_W);
    $display("%m mod2: params p2 ADDR_W %0d DATA_W %0d", p2.ADDR_W, p2.DATA_W);
  end

endmodule

module t;
  common_intf #(8, 16) i1_2 ();  // connects m1 to m2
  common_intf #(4, 32) i2_3 ();  // connects m2 to m3
  mod1 m1 (i1_2);
  mod2 m2 (
      i1_2,
      i2_3
  );
  mod1 m3 (i2_3);
  initial begin
    #10;
    $finish;
  end
endmodule
