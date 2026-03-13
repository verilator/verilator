// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  rand bit l;
  rand bit x;
  rand bit w;
  rand bit r;
} reg_t;

typedef struct packed {
  bit l;
  bit x;
  bit w;
  bit r;
} preg_t;

module t;
  class item;
    rand bit [3:0] mode;
    rand bit [7:0] data[4];
    rand int x;
    rand int y;
    rand int arr[4];

    constraint mode_c {
      mode inside {[0:3]};
    }

    constraint data_c {
      foreach (data[i]) {
        solve mode before data[i];
        if (mode == 0)
          data[i] == 8'h00;
        else
          data[i] inside {[8'd1:8'd255]};
      }
    }

    // Static array index in solve...before (non-foreach)
    constraint arr_c {
      solve arr[0] before y;
    }
  endclass

  class Packet;
    rand bit [7:0] pdata[5];
    rand bit px;
    rand reg_t cfg[3];
    rand preg_t pcfg[3];

    constraint c_pdata {
      foreach (pdata[i]) {
        solve px before pdata[i];
        pdata[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50};
      }
    }

    constraint c_cfg {
      foreach (cfg[i]) {
        solve px before cfg[i].w, cfg[i].r;
        solve cfg[i].l before cfg[i].x;
      }
    }

    constraint c_pcfg {
      foreach (pcfg[i]) {
        solve px before pcfg[i].w, pcfg[i].r;
        solve pcfg[i].l before pcfg[i].x;
      }
    }
  endclass

  initial begin
    static item it = new;
    static Packet pkt = new;

    // Test 1: solve...before with conditional constraints
    repeat (20) begin
      `checkd(it.randomize(), 1);
      if (it.mode == 0) begin
        foreach (it.data[i]) begin
          `checkh(it.data[i], 8'h00);
        end
      end
    end

    // Test 2: solve...before with unpacked/packed struct array members
    repeat (20) begin
      `checkd(pkt.randomize(), 1);
      foreach (pkt.pdata[i]) begin
        `checkd(pkt.pdata[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50}, 1);
      end
    end

    // Test 3: solve...before with static array index (non-foreach)
    repeat (20) begin
      `checkd(it.randomize(), 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
