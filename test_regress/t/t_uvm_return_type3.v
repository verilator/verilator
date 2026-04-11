// DESCRIPTION: Verilator: Verify parameterized class self-referential return
// types across a variety of value-parameter types (keyword, ranged, signed).
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  // Keyword type: bit (1-bit unsigned)
  class cls_bit #(
      bit P = 1
  );
    static function cls_bit#(P) f();
      cls_bit #(P) c = new();
      return c;
    endfunction
  endclass

  // Keyword type: byte (8-bit signed)
  class cls_byte #(
      byte P = 8'd1
  );
    static function cls_byte#(P) f();
      cls_byte #(P) c = new();
      return c;
    endfunction
  endclass

  // Keyword type: shortint (16-bit signed)
  class cls_shortint #(
      shortint P = 16'd1
  );
    static function cls_shortint#(P) f();
      cls_shortint #(P) c = new();
      return c;
    endfunction
  endclass

  // Keyword type: integer (32-bit signed)
  class cls_integer #(
      integer P = 1
  );
    static function cls_integer#(P) f();
      cls_integer #(P) c = new();
      return c;
    endfunction
  endclass

  // Explicit range: logic [15:0] (16-bit unsigned)
  class cls_logic16 #(
      logic [15:0] P = 16'd1
  );
    static function cls_logic16#(P) f();
      cls_logic16 #(P) c = new();
      return c;
    endfunction
  endclass

  // Explicit range: logic [31:0] (32-bit unsigned)
  class cls_logic32 #(
      logic [31:0] P = 1
  );
    static function cls_logic32#(P) f();
      cls_logic32 #(P) c = new();
      return c;
    endfunction
  endclass

  initial begin
    // verilog_format: off
    static cls_bit#(0)          c1 = cls_bit#(0)::f();
    static cls_byte#(8'd0)      c2 = cls_byte#(8'd0)::f();
    static cls_shortint#(16'd0) c3 = cls_shortint#(16'd0)::f();
    static cls_integer#(0)      c4 = cls_integer#(0)::f();
    static cls_logic16#(16'd0)  c5 = cls_logic16#(16'd0)::f();
    static cls_logic32#(0)      c6 = cls_logic32#(0)::f();
    // verilog_format: off

    if (c1 == null || c2 == null || c3 == null
        || c4 == null || c5 == null || c6 == null) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
