// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

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
  int ok;

  initial begin
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
