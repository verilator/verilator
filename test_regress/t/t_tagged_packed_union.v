// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test packed tagged unions for coverage

module t;
  typedef union tagged packed {
    void A;
    logic [7:0] B;
    logic [15:0] C;
  } PackedTagged;

  PackedTagged p;
  int errors = 0;

  initial begin
    // Test 8-bit member
    p = tagged B (8'hAB);
    if (p matches tagged B .val) begin
      if (val !== 8'hAB) begin
        $display("ERROR: Expected B=0xAB, got 0x%h", val);
        errors++;
      end
    end else begin
      $display("ERROR: Expected tagged B");
      errors++;
    end

    // Test 16-bit member (widest)
    p = tagged C (16'h1234);
    if (p matches tagged C .val) begin
      if (val !== 16'h1234) begin
        $display("ERROR: Expected C=0x1234, got 0x%h", val);
        errors++;
      end
    end else begin
      $display("ERROR: Expected tagged C");
      errors++;
    end

    // Test case statement with packed union
    p = tagged B (8'h55);
    case (p) matches
      tagged B .x: begin
        if (x !== 8'h55) begin
          $display("ERROR: Case B expected 0x55, got 0x%h", x);
          errors++;
        end
      end
      tagged C .x: begin
        $display("ERROR: Should not match C");
        errors++;
      end
      default: begin
        $display("ERROR: Should match B");
        errors++;
      end
    endcase

    if (errors == 0) begin
      $write("*-* All Finished *-*\n");
    end
    $finish;
  end
endmodule
