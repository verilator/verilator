// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  bit clk;
  int cyc;

  always #1 clk = !clk;

  bit rst_mod;
  int before_mod_false;
  int before_mod_gen_false;
  int before_gen_default_false;
  int before_gen_child_default_false;
  int prog_false_count;

  always_comb rst_mod = (cyc < 3);

  // The default declaration appears later in the module, but still applies here.
  assert property (@(posedge clk) 0)
    else before_mod_false++;

  generate
    begin : g_before_mod_default
      // Inherits the module default declaration that appears later in this module.
      assert property (@(posedge clk) 0)
        else before_mod_gen_false++;
    end

    begin : g_before_local_default
      // The generate-local default declaration appears later in the block.
      assert property (@(posedge clk) 0)
        else before_gen_default_false++;

      begin : g_child_inherit
        // Inherits the generate-local default declaration that appears later.
        assert property (@(posedge clk) 0)
          else before_gen_child_default_false++;
      end
      default disable iff (cyc < 7);
    end
  endgenerate

  default disable iff (rst_mod);

  generate
    begin : g_override
      bit rst_gen;
      int override_false;

      always_comb rst_gen = (cyc < 5);

      default disable iff (rst_gen);

      assert property (@(posedge clk) 0)
        else override_false++;
    end

    begin : g_inherit
      bit rst_mod;
      int inherit_false;

      always_comb rst_mod = (cyc < 8);

      // Inherits the module default, whose rst_mod was resolved in module scope.
      assert property (@(posedge clk) 0)
        else inherit_false++;
    end
  endgenerate

  if_scope u_if (.clk(clk), .cyc(cyc));
  p_scope u_prog (.clk(clk), .cyc(cyc), .false_count(prog_false_count));
  examples_with_default_count u_with (.clk(clk), .cyc(cyc));
  examples_without_default_count u_without (.clk(clk), .cyc(cyc));
  examples_with_default u_ieee_with (.a(1'b0), .b(1'b0), .clk(clk), .rst(1'b0), .rst1(1'b0));
  examples_without_default u_ieee_without (.a(1'b0), .b(1'b0), .clk(clk), .rst(1'b0));
  m_override u_m_override (.clk(clk), .cyc(cyc));

  // The disable iff expression is unsampled, so same-edge updates race in MT simulation.
  // Change clk on negedge while the properties are sampled on posedge to avoid races.
  always @(negedge clk) begin
    cyc++;
    if (cyc == 12) begin
      `checkd(before_mod_false, 9);
      `checkd(before_mod_gen_false, 9);
      `checkd(before_gen_default_false, 5);
      `checkd(before_gen_child_default_false, 5);
      `checkd(g_inherit.inherit_false, 9);
      `checkd(g_override.override_false, 7);
      `checkd(u_if.false_count, 6);
      `checkd(u_if.g_inherit.false_count, 6);
      `checkd(prog_false_count, 4);
      `checkd(u_with.explicit_assert_false, 5);
      `checkd(u_with.explicit_property_false, 5);
      `checkd(u_with.inferred_default_false, 9);
      `checkd(u_without.explicit_assert_false, 9);
      `checkd(u_without.explicit_property_false, 9);
      `checkd(u_m_override.false_count, 7);
      `checkd(u_m_override.g_inherit_from_module.false_count, 7);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module examples_with_default (input logic a, b, clk, rst, rst1);
default disable iff rst;
property p1;
disable iff (rst1) a |=> b;
endproperty
// Disable condition is rst1 - explicitly specified within a1
a1 : assert property (@(posedge clk) disable iff (rst1) a |=> b);
// Disable condition is rst1 - explicitly specified within p1
a2 : assert property (@(posedge clk) p1);
// Disable condition is rst - no explicit specification, inferred from
// default disable iff declaration
a3 : assert property (@(posedge clk) a |=> b);
// Disable condition is 1'b0. This is the only way to
// cancel the effect of default disable.
a4 : assert property (@(posedge clk) disable iff (1'b0) a |=> b);
endmodule

module examples_without_default (input logic a, b, clk, rst);
property p2;
disable iff (rst) a |=> b;
endproperty
// Disable condition is rst - explicitly specified within a5
a5 : assert property (@(posedge clk) disable iff (rst) a |=> b);
// Disable condition is rst - explicitly specified within p2
a6 : assert property (@ (posedge clk) p2);
// No disable condition
a7 : assert property (@ (posedge clk) a |=> b);
endmodule

module examples_with_default_count(input bit clk, input int cyc);
  int explicit_assert_false;
  int explicit_property_false;
  int inferred_default_false;

  default disable iff (cyc < 3);

  property p1;
    disable iff (cyc < 7) 0;
  endproperty

  // Disable condition is explicit in the assertion.
  assert property (@(posedge clk) disable iff (cyc < 7) 0)
    else explicit_assert_false++;

  // Disable condition is explicit in the property.
  assert property (@(posedge clk) p1)
    else explicit_property_false++;

  // Disable condition is inferred from the default.
  assert property (@(posedge clk) 0)
    else inferred_default_false++;

endmodule

module examples_without_default_count(input bit clk, input int cyc);
  int explicit_assert_false;
  int explicit_property_false;

  property p2;
    disable iff (cyc < 3) 0;
  endproperty

  // Disable condition is explicit in the assertion.
  assert property (@(posedge clk) disable iff (cyc < 3) 0)
    else explicit_assert_false++;

  // Disable condition is explicit in the property.
  assert property (@(posedge clk) p2)
    else explicit_property_false++;

endmodule

module m_override(input bit clk, input int cyc);
  bit rst2;
  int false_count;

  always_comb rst2 = (cyc < 5);
  default disable iff (rst2);

  assert property (@(posedge clk) 0)
    else false_count++;

  generate
    begin : g_inherit_from_module
      int false_count;
      assert property (@(posedge clk) 0)
        else false_count++;
    end
  endgenerate
endmodule

interface if_scope(input bit clk, input int cyc);
  bit rst_if;
  int false_count;

  always_comb rst_if = (cyc < 6);
  default disable iff (rst_if);

  assert property (@(posedge clk) 0)
    else false_count++;

  generate
    begin : g_inherit
      int false_count;
      assert property (@(posedge clk) 0)
        else false_count++;
    end
  endgenerate
endinterface

program p_scope(input bit clk, input int cyc,
                output int false_count);
  default disable iff (cyc < 8);

  assert property (@(posedge clk) 0)
    else false_count++;
endprogram
