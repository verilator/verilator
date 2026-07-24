// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Aliases with distinct dtypes, identical C storage (retargeted)
module t (
  input  logic                clk,
  input  logic signed  [7:0]  in_signed,
  input  logic         [7:0]  in_enum,
  input  logic signed [31:0]  in_int,
  input  logic         [7:0]  in_unsigned,
  input  logic         [7:0]  in_logic,
  output logic         [7:0]  o
);

  typedef enum logic [7:0] { E_LO = 8'd10, E_MID = 8'd100, E_HI = 8'd200 } e_t;

  // Sequential sources (canonical for aliases)
  logic signed [7:0] signed_src;
  e_t                enum_var;
  integer            integer_var;
  logic        [7:0] unsigned_src;
  logic        [7:0] logic_src;

  always_ff @(posedge clk) begin
    signed_src   <= in_signed;
    enum_var     <= e_t'(in_enum);
    integer_var  <= in_int;
    unsigned_src <= in_unsigned;
    logic_src    <= in_logic;
  end

  // Bare-copy aliases
  logic        [7:0] a_sign;   assign a_sign  = signed_src;
  logic        [7:0] a_enum;   assign a_enum  = enum_var;
  int                a_ii;     assign a_ii    = integer_var;
  logic signed [7:0] a_ssign;  assign a_ssign = unsigned_src;
  bit          [7:0] a_bit;    assign a_bit   = logic_src;

  assign o = signed_src ^ enum_var ^ integer_var[7:0] ^ unsigned_src ^ logic_src;

endmodule
