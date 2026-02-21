// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// DESCRIPTION: Minimal test for sibling interface typedef resolution
// This is the SIMPLEST case that demonstrates the t_lparam_dep_iface10 failure pattern:
// - Two sibling cells of the same interface type with DIFFERENT parameters
// - A module that accesses typedefs from BOTH siblings
//

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// Parameterized interface with a typedef that depends on the parameter
interface a_if #(parameter int WIDTH = 8)();
  localparam LP_WIDTH = WIDTH*2;
  typedef logic [LP_WIDTH-1:0] data_t;
  data_t data;
endinterface

// Wrapper interface with TWO SIBLING instances of a_if with DIFFERENT widths
interface wrapper_if #(parameter int WIDTH_A = 8, parameter int WIDTH_B = 16)();
  a_if #(.WIDTH(WIDTH_A)) a_inst();
  a_if #(.WIDTH(WIDTH_B)) b_inst();

  // Re-export typedefs from each sibling
  typedef a_inst.data_t a_data_t;
  typedef b_inst.data_t b_data_t;
endinterface

// Module that accesses typedefs from BOTH siblings via interface port
module consumer (
  wrapper_if wif
);
  // These MUST resolve to DIFFERENT types
  typedef wif.a_inst.data_t local_a_t;  // Should be 10 bits
  typedef wif.b_inst.data_t local_b_t;  // Should be 20 bits

  local_a_t val_a;
  local_b_t val_b;

  initial begin
    #1;
    `checkd($bits(local_a_t), 20);
    `checkd($bits(local_b_t), 40);
  end
endmodule

// Top module
module t();
  wrapper_if #(.WIDTH_A(10), .WIDTH_B(20)) wif();
  consumer c(.wif(wif));

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
