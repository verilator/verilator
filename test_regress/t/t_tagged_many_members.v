// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged union with >8 members requiring multi-bit tag

module t;
  // 9 members requires 4-bit tag (ceil(log2(9)) = 4)
  typedef union tagged {
    void M0;
    void M1;
    void M2;
    void M3;
    void M4;
    void M5;
    void M6;
    void M7;
    int M8;  // 9th member with data
  } ManyMembers;

  ManyMembers m;
  int errors = 0;

  initial begin
    // Test first void member using case
    m = tagged M0;
    case (m) matches
      tagged M0: begin /* Expected */ end
      default: begin $display("ERROR: Expected tagged M0"); errors++; end
    endcase

    // Test middle void member using case
    m = tagged M4;
    case (m) matches
      tagged M4: begin /* Expected */ end
      default: begin $display("ERROR: Expected tagged M4"); errors++; end
    endcase

    // Test last void member using case
    m = tagged M7;
    case (m) matches
      tagged M7: begin /* Expected */ end
      default: begin $display("ERROR: Expected tagged M7"); errors++; end
    endcase

    // Test 9th member with data
    m = tagged M8 (12345);
    if (m matches tagged M8 .val) begin
      if (val !== 12345) begin
        $display("ERROR: Expected M8=12345, got %d", val);
        errors++;
      end
    end else begin
      $display("ERROR: Expected tagged M8");
      errors++;
    end

    // Test case with many members
    m = tagged M5;
    case (m) matches
      tagged M0: begin $display("ERROR: Should not match M0"); errors++; end
      tagged M1: begin $display("ERROR: Should not match M1"); errors++; end
      tagged M2: begin $display("ERROR: Should not match M2"); errors++; end
      tagged M3: begin $display("ERROR: Should not match M3"); errors++; end
      tagged M4: begin $display("ERROR: Should not match M4"); errors++; end
      tagged M5: begin /* Expected */ end
      tagged M6: begin $display("ERROR: Should not match M6"); errors++; end
      tagged M7: begin $display("ERROR: Should not match M7"); errors++; end
      tagged M8 .x: begin $display("ERROR: Should not match M8"); errors++; end
    endcase

    // Test negative match - ensure different tags don't match (use case)
    m = tagged M8 (999);
    case (m) matches
      tagged M0: begin $display("ERROR: M8 should not match M0"); errors++; end
      tagged M7: begin $display("ERROR: M8 should not match M7"); errors++; end
      tagged M8 .x: begin
        if (x !== 999) begin
          $display("ERROR: Expected M8=999, got %d", x);
          errors++;
        end
      end
      default: begin $display("ERROR: Unexpected tag"); errors++; end
    endcase

    if (errors == 0) begin
      $write("*-* All Finished *-*\n");
    end
    $finish;
  end
endmodule
