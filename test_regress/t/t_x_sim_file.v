// DESCRIPTION: Verilator: Test X/Z four-state simulation with file output
//
// This test verifies four-state simulation with $fwrite, $fdisplay.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

  integer fd;
  string filename = "/tmp/verilator_xz_test.txt";
  
  // Four-state signals
  reg [3:0] a = 4'b1010;
  reg [3:0] x = 4'b1X10;
  reg [3:0] z = 4'bZ010;
  reg [7:0] xz_data = 8'bXZ10XZ10;
  
  initial begin
    fd = $fopen(filename, "w");
    if (fd == 0) begin
      $display("ERROR: Could not open file %s", filename);
      $finish;
    end
    
    $fwrite(fd, "=== File Output Test with X/Z ===\n");
    $fwrite(fd, "a = %b (initialized)\n", a);
    $fwrite(fd, "x = %b (has X)\n", x);
    $fwrite(fd, "z = %b (has Z)\n", z);
    $fwrite(fd, "xz_data = %b (mixed X/Z)\n", xz_data);
    
    // Test operations with X/Z and write results
    $fwrite(fd, "\n=== Operations ===\n");
    $fwrite(fd, "a & x = %b\n", a & x);
    $fwrite(fd, "a | z = %b\n", a | z);
    $fwrite(fd, "x ^ z = %b\n", x ^ z);
    $fwrite(fd, "x + z = %b\n", x + z);
    
    // Test $fdisplay
    $fwrite(fd, "\n=== Using $fdisplay ===\n");
    $fdisplay(fd, "Display with x: %b", x);
    $fdisplay(fd, "Display with z: %b", z);
    $fdisplay(fd, "Display with xz_data: %b", xz_data);
    
    // Test $fwrite with hex format
    $fwrite(fd, "\n=== Hex Format ===\n");
    $fwrite(fd, "a = %h\n", a);
    $fwrite(fd, "x = %h (X becomes 0 in hex)\n", x);
    $fwrite(fd, "z = %h (Z becomes 0 in hex)\n", z);
    
    // Test uninitialized signal
    reg [3:0] uninit;
    $fwrite(fd, "\n=== Uninitialized Signal ===\n");
    $fwrite(fd, "uninit (4-state default) = %b\n", uninit);
    
    $fclose(fd);
    
    $display("Wrote X/Z test output to %s", filename);
    $display("Contents:");
    $display("");
    
    // Read and display the file contents
    string line;
    fd = $fopen(filename, "r");
    while ($fgets(line, fd)) begin
      $display("%s", line);
    end
    $fclose(fd);
    
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
