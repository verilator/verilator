// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.
//
// bug445

`define WIDTH  12
`define SEL_NUM_BITS `WIDTH-`SEL_NUM_BITS +: `SEL_NUM_BITS
`define SEL_BITS     `WIDTH-`SEL_NUM_BITS +: `SEL_NUM_BITS
`define ADDR_BITS    0 +: `WIDTH-`SEL_NUM_BITS

typedef logic [`SEL_NUM_BITS-1:0]  d_t;
