// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test passing sub-interface of LOCAL instance to child module
// Works with both inline (default) and -fno-inline

interface base_reg_if;
  typedef struct packed { logic [7:0] scratch; } wr_t;
  typedef struct packed { logic [7:0] version; logic [7:0] scratch_rb; } rd_t;
  wr_t wr;
  rd_t rd;
endinterface

interface app_reg_if;
  base_reg_if base();
endinterface

interface level1_if;
  logic [7:0] data;
endinterface

interface level2_if;
  level1_if l1();
endinterface

interface level3_if;
  level2_if l2();
endinterface

module base_regs (input wire i_clk, base_reg_if i_base);
  always_ff @(posedge i_clk) begin
    i_base.rd.version    <= 8'h42;
    i_base.rd.scratch_rb <= i_base.wr.scratch;
  end
endmodule

module base_observer (base_reg_if i_base, output logic [7:0] o_wr_val, o_rd_val);
  assign o_wr_val = i_base.wr.scratch;
  assign o_rd_val = i_base.rd.version;
endmodule

module level1_driver (level1_if i_l1, input logic [7:0] val);
  assign i_l1.data = val;
endmodule

module t;
  logic clk = 0;
  int   cyc = 0;

  // Local interface instances
  app_reg_if w_app_reg_if();
  level3_if l3();
  level2_if l2_another();

  // Pass nested interface from local instance to child modules
  base_regs m_base_regs (.i_clk(clk), .i_base(w_app_reg_if.base));

  logic [7:0] obs_wr_val, obs_rd_val;
  base_observer m_base_obs (.i_base(w_app_reg_if.base), .o_wr_val(obs_wr_val), .o_rd_val(obs_rd_val));

  // Deep nesting: l3.l2.l1
  level1_driver m_l1_drv(l3.l2.l1, 8'hAB);
  level1_driver m_l1_drv2(l2_another.l1, 8'hCD);

  always #5 clk = ~clk;

  logic [7:0] exp_scratch, exp_scratch_d1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    exp_scratch    <= cyc[7:0];
    exp_scratch_d1 <= exp_scratch;

    w_app_reg_if.base.wr.scratch <= cyc[7:0];

    if (cyc > 3) begin
      if (w_app_reg_if.base.rd.version !== 8'h42) begin
        $display("FAIL cyc=%0d: version=%h expected 42", cyc, w_app_reg_if.base.rd.version);
        $stop;
      end
      if (w_app_reg_if.base.rd.scratch_rb !== exp_scratch_d1) begin
        $display("FAIL cyc=%0d: scratch_rb=%h expected %h", cyc, w_app_reg_if.base.rd.scratch_rb, exp_scratch_d1);
        $stop;
      end
      if (obs_wr_val !== exp_scratch) begin
        $display("FAIL cyc=%0d: obs_wr_val=%h expected %h", cyc, obs_wr_val, exp_scratch);
        $stop;
      end
      if (obs_rd_val !== 8'h42) begin
        $display("FAIL cyc=%0d: obs_rd_val=%h expected 42", cyc, obs_rd_val);
        $stop;
      end
      if (l3.l2.l1.data !== 8'hAB) begin
        $display("FAIL cyc=%0d: l3.l2.l1.data=%h expected AB", cyc, l3.l2.l1.data);
        $stop;
      end
      if (l2_another.l1.data !== 8'hCD) begin
        $display("FAIL cyc=%0d: l2_another.l1.data=%h expected CD", cyc, l2_another.l1.data);
        $stop;
      end
    end

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
