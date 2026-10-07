// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class MixedShift #(
    parameter int WIDTH = 7,
    parameter int SHIFT_WIDTH = 32
);
  rand bit [WIDTH-1:0] prot;
  rand bit signed [WIDTH-1:0] signed_prot;
  bit [SHIFT_WIDTH-1:0] amount;
  rand bit [SHIFT_WIDTH-1:0] rand_amount;
  bit signed [WIDTH-1:0] expected_signed;

  task run;
    int randomize_result;
    bit [WIDTH-1:0] actual;
    // Include amounts whose high bits cannot be discarded when matching SMT sorts.
    for (int shift_case = 0; shift_case < 5; shift_case++) begin
      case (shift_case)
        0: amount = 0;
        1: amount = SHIFT_WIDTH'(4);
        2: amount = SHIFT_WIDTH'(WIDTH);
        3: amount = SHIFT_WIDTH'(128);
        4: amount = '1;
      endcase
      repeat (10) begin
        randomize_result = randomize() with {(prot >> amount) == '0;};
        `checkh(randomize_result, 1);
        actual = prot >> amount;
        `checkh(actual, '0);

        randomize_result = randomize() with {
          rand_amount == amount;
          (prot >> rand_amount) == '0;
        };
        `checkh(randomize_result, 1);
        actual = prot >> rand_amount;
        `checkh(actual, '0);

        randomize_result = randomize() with {(prot << amount) == '0;};
        `checkh(randomize_result, 1);
        actual = prot << amount;
        `checkh(actual, '0);

        randomize_result = randomize() with {
          rand_amount == amount;
          (prot << rand_amount) == '0;
        };
        `checkh(randomize_result, 1);
        actual = prot << rand_amount;
        `checkh(actual, '0);

        // Nested shifts revisit the result-width selection inside another shift.
        randomize_result = randomize() with {
          rand_amount == amount;
          ((prot >> rand_amount) >> amount) == '0;
        };
        `checkh(randomize_result, 1);
        actual = (prot >> rand_amount) >> amount;
        `checkh(actual, '0);

        // Also exercise a compound shift amount rather than a bare member.
        randomize_result = randomize() with {
          rand_amount == amount;
          (prot << (rand_amount | amount)) == '0;
        };
        `checkh(randomize_result, 1);
        actual = prot << (rand_amount | amount);
        `checkh(actual, '0);

        expected_signed = WIDTH'(-37);
        expected_signed = expected_signed >>> amount;
        randomize_result = randomize() with {
          signed_prot == WIDTH'(-37);
          (signed_prot >>> amount) == expected_signed;
        };
        `checkh(randomize_result, 1);
        actual = signed_prot >>> amount;
        `checkh(actual, expected_signed);

        randomize_result = randomize() with {
          rand_amount == amount;
          signed_prot == WIDTH'(-37);
          (signed_prot >>> rand_amount) == expected_signed;
        };
        `checkh(randomize_result, 1);
        actual = signed_prot >>> rand_amount;
        `checkh(actual, expected_signed);
      end
    end
  endtask
endclass

class AlignedPacket;
  localparam int ADDRW = 37;
  localparam int SIZEW = 4;

  typedef logic [ADDRW-1:0] address_t;
  typedef logic [SIZEW-1:0] size_t;

  rand address_t address;
  rand size_t    size;

  // Constraint with mixed-width shift: address is 37-bit, size is 4-bit
  // The expression (1 << size) involves a width mismatch that must be
  // handled by zero-extending the shift RHS to match LHS width.
  constraint c_aligned {
    address % (1 << size) == 0;
  }
endclass

class ConstShiftPacket;
  localparam int ADDRW = 37;

  typedef logic [ADDRW-1:0] address_t;

  rand address_t address;

  // Constraint with constant shift amount (different width from address)
  constraint c_aligned {
    address % (1 << 10) == 0;
  }
endclass

class ImplicationShift;
  localparam int ADDRW = 37;
  localparam int SIZEW = 4;

  typedef logic [ADDRW-1:0] address_t;
  typedef logic [SIZEW-1:0] size_t;
  typedef enum {
    TXN_READ, TXN_WRITE, TXN_IDLE
  } txn_type_t;

  rand txn_type_t txn_type;
  rand size_t     size;
  rand address_t  address;

  // Implication with mixed-width shift in consequent
  constraint c_addr {
    txn_type inside {TXN_READ, TXN_WRITE} -> address % (1 << size) == 0;
  }
endclass

module t;
  AlignedPacket pkt1;
  ConstShiftPacket pkt2;
  ImplicationShift pkt3;
  MixedShift #(7, 32) mixed7;
  MixedShift #(1, 32) mixed1;
  MixedShift #(31, 65) mixed31;
  MixedShift #(65, 32) mixed65;
  MixedShift #(7, 7) equal7;
  int ok;
  int unsigned width = 4;

  initial begin
    mixed7 = new;
    repeat (10) begin
      ok = mixed7.randomize() with {(prot >> width) == '0;};
      `checkh(ok, 1);
      `checkh(mixed7.prot < 16, 1);
    end
    mixed1 = new;
    mixed31 = new;
    mixed65 = new;
    equal7 = new;
    mixed7.run();
    mixed1.run();
    mixed31.run();
    mixed65.run();
    equal7.run();
    // Test 1: Variable shift amount with mixed widths
    pkt1 = new;
    pkt1.size = 6;
    ok = pkt1.randomize() with { size == 6; };
    if (ok != 1) begin
      $display("ERROR: Test 1 randomize failed");
      $stop;
    end
    // address must be aligned to 1<<6 = 64
    if (pkt1.address % 64 != 0) begin
      $display("ERROR: Test 1 alignment check failed: address=0x%0h", pkt1.address);
      $stop;
    end

    // Test 2: Unconstrained randomize (variable shift)
    pkt1 = new;
    ok = pkt1.randomize();
    if (ok != 1) begin
      $display("ERROR: Test 2 randomize failed");
      $stop;
    end
    // address must be aligned to 1<<size
    if (pkt1.address % (37'(1) << pkt1.size) != 0) begin
      $display("ERROR: Test 2 alignment check failed: address=0x%0h size=%0d",
               pkt1.address, pkt1.size);
      $stop;
    end

    // Test 3: Constant shift amount with wide address
    pkt2 = new;
    ok = pkt2.randomize();
    if (ok != 1) begin
      $display("ERROR: Test 3 randomize failed");
      $stop;
    end
    // address must be aligned to 1<<10 = 1024
    if (pkt2.address % 1024 != 0) begin
      $display("ERROR: Test 3 alignment check failed: address=0x%0h", pkt2.address);
      $stop;
    end

    // Test 4: Implication with mixed-width shift
    pkt3 = new;
    ok = pkt3.randomize() with { txn_type == ImplicationShift::TXN_READ; size == 4; };
    if (ok != 1) begin
      $display("ERROR: Test 4 randomize failed");
      $stop;
    end
    // When txn_type is TXN_READ, address must be aligned to 1<<4 = 16
    if (pkt3.address % 16 != 0) begin
      $display("ERROR: Test 4 alignment check failed: address=0x%0h", pkt3.address);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
