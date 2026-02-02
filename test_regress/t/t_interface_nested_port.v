// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Test passing sub-interface of INTERFACE PORT to child module
// Only works with inline (default); -fno-inline is not supported

interface base_reg_if;
  typedef struct packed { logic [7:0] scratch; } wr_t;
  typedef struct packed { logic [7:0] version; logic [7:0] scratch_rb; } rd_t;
  wr_t wr;
  rd_t rd;
endinterface

interface example_reg_if;
  typedef struct packed { logic enable; logic [6:0] cfg; } wr_t;
  typedef struct packed { logic busy; logic [6:0] status; } rd_t;
  wr_t wr;
  rd_t rd;
endinterface

interface app_reg_if;
  base_reg_if base();
  example_reg_if example();
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

module example_regs (input wire i_clk, example_reg_if i_example);
  always_ff @(posedge i_clk) begin
    i_example.rd.busy   <= i_example.wr.enable;
    i_example.rd.status <= i_example.wr.cfg;
  end
endmodule

// Key test: module with interface PORT passes nested interface to submodule
module app_top (
  input wire         i_clk,
  app_reg_if         i_app,
  output logic [7:0] o_obs_wr,
  output logic [7:0] o_obs_rd
);
  base_observer m_base_obs (
    .i_base(i_app.base),
    .o_wr_val(o_obs_wr),
    .o_rd_val(o_obs_rd)
  );

  example_regs m_example_regs (
    .i_clk(i_clk),
    .i_example(i_app.example)
  );
endmodule

module t;
  logic clk = 0;
  int   cyc = 0;

  app_reg_if w_app_reg_if();

  // Drive base_regs directly from TB (local instance case, for reference)
  base_regs m_base_regs (.i_clk(clk), .i_base(w_app_reg_if.base));

  // Pass full interface to app_top, which passes nested interfaces to submodules
  logic [7:0] app_obs_wr, app_obs_rd;
  app_top m_app_top (
    .i_clk(clk),
    .i_app(w_app_reg_if),
    .o_obs_wr(app_obs_wr),
    .o_obs_rd(app_obs_rd)
  );

  always #5 clk = ~clk;

  logic [7:0] exp_scratch, exp_scratch_d1;
  logic [6:0] exp_cfg, exp_cfg_d1;
  logic       exp_enable, exp_enable_d1;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    exp_scratch    <= cyc[7:0];
    exp_scratch_d1 <= exp_scratch;
    exp_cfg        <= cyc[6:0];
    exp_cfg_d1     <= exp_cfg;
    exp_enable     <= cyc[0];
    exp_enable_d1  <= exp_enable;

    w_app_reg_if.base.wr.scratch   <= cyc[7:0];
    w_app_reg_if.example.wr.enable <= cyc[0];
    w_app_reg_if.example.wr.cfg    <= cyc[6:0];

    if (cyc > 3) begin
      // Verify base_regs output
      if (w_app_reg_if.base.rd.version !== 8'h42) begin
        $display("FAIL cyc=%0d: version=%h expected 42", cyc, w_app_reg_if.base.rd.version);
        $stop;
      end
      if (w_app_reg_if.base.rd.scratch_rb !== exp_scratch_d1) begin
        $display("FAIL cyc=%0d: scratch_rb=%h expected %h", cyc, w_app_reg_if.base.rd.scratch_rb, exp_scratch_d1);
        $stop;
      end

      // Verify example_regs output (driven through app_top)
      if (w_app_reg_if.example.rd.busy !== exp_enable_d1) begin
        $display("FAIL cyc=%0d: busy=%b expected %b", cyc, w_app_reg_if.example.rd.busy, exp_enable_d1);
        $stop;
      end
      if (w_app_reg_if.example.rd.status !== exp_cfg_d1) begin
        $display("FAIL cyc=%0d: status=%h expected %h", cyc, w_app_reg_if.example.rd.status, exp_cfg_d1);
        $stop;
      end

      // Verify observer inside app_top (the key test - nested port passthrough)
      if (app_obs_wr !== exp_scratch) begin
        $display("FAIL cyc=%0d: app_obs_wr=%h expected %h", cyc, app_obs_wr, exp_scratch);
        $stop;
      end
      if (app_obs_rd !== 8'h42) begin
        $display("FAIL cyc=%0d: app_obs_rd=%h expected 42", cyc, app_obs_rd);
        $stop;
      end
    end

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
