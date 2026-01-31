// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test nested struct pattern matching with tagged unions

module t;
  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } Inner;

  typedef union tagged {
    void Empty;   // Void first like working tests
    Inner Data;
  } Outer;

  Outer o;
  int errors = 0;
  logic [7:0] x, y;

  initial begin
    // Test struct member assignment and pattern matching
    o = tagged Data '{8'h12, 8'h34};

    if (o matches tagged Data .inner) begin
      if (inner.a !== 8'h12 || inner.b !== 8'h34) begin
        $display("ERROR: Expected Data '{0x12, 0x34}, got '{0x%h, 0x%h}", inner.a, inner.b);
        errors++;
      end
    end else begin
      $display("ERROR: Expected tagged Data");
      errors++;
    end

    // Test void member using case (more reliable)
    o = tagged Empty;
    case (o) matches
      tagged Empty: begin
        // Expected
      end
      tagged Data .d: begin
        $display("ERROR: Empty should not match Data");
        errors++;
      end
    endcase

    // Test case with nested struct
    o = tagged Data '{8'hAB, 8'hCD};
    case (o) matches
      tagged Empty: begin
        $display("ERROR: Should not match Empty");
        errors++;
      end
      tagged Data .d: begin
        if (d.a !== 8'hAB || d.b !== 8'hCD) begin
          $display("ERROR: Case expected '{0xAB, 0xCD}, got '{0x%h, 0x%h}", d.a, d.b);
          errors++;
        end
      end
    endcase

    if (errors == 0) begin
      $write("*-* All Finished *-*\n");
    end
    $finish;
  end
endmodule
