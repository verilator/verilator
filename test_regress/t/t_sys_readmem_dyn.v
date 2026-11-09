// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define STRINGIFY(x) `"x`"
// verilog_format: on

module t;
  initial begin
    begin
      logic [7:0] mem[];
      int fd;
      fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn.hex"}, "w");
      $fdisplay(fd, "11\n22\n33\n44");
      $fclose(fd);
      mem = new[4];
      $readmemh({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn.hex"}, mem);
      `checkh(mem[0], 8'h11);
      `checkh(mem[1], 8'h22);
      `checkh(mem[3], 8'h44);
    end

    begin
      // Typedef'd array, narrow odd width, file longer than the array
      typedef logic [6:0] dyn7_t[];
      dyn7_t mem7;
      int fd;
      fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn_7.hex"}, "w");
      $fdisplay(fd, "01\n02\n03");
      $fclose(fd);
      mem7 = new[2];
      $readmemh({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn_7.hex"}, mem7);
      `checkh(mem7[0], 7'h01);
      `checkh(mem7[1], 7'h02);
      // Ranges and empty array
      $writememh({`STRINGIFY(`TEST_OBJ_DIR), "/writemem_dyn_d.hex"}, mem7, 1, 0);
      $writememh({`STRINGIFY(`TEST_OBJ_DIR), "/writemem_dyn_a.hex"}, mem7);
      mem7 = new[0];
      $writememh({`STRINGIFY(`TEST_OBJ_DIR), "/writemem_dyn_empty.hex"}, mem7);
    end

    begin
      // Wide, typedef, start address and round trip through $writemem
      typedef logic [64:0] wide_t;
      wide_t wmem[];
      wide_t rmem[];
      int fd;
      fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn_w.hex"}, "w");
      $fdisplay(fd, "1_0000_0001\n2_0000_0002\n3_0000_0003\n4_0000_0004");
      $fclose(fd);
      wmem = new[5];
      $readmemh({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn_w.hex"}, wmem, 1);
      `checkh(wmem[0], 65'h0);
      `checkh(wmem[1], 65'h1_0000_0001);
      `checkh(wmem[3], 65'h3_0000_0003);
      `checkh(wmem[4], 65'h4_0000_0004);
      $writememh({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn_o.hex"}, wmem, 1, 3);
      rmem = new[4];
      $readmemh({`STRINGIFY(`TEST_OBJ_DIR), "/readmem_dyn_o.hex"}, rmem);
      `checkh(rmem[0], 65'h1_0000_0001);
      `checkh(rmem[2], 65'h3_0000_0003);
      `checkh(rmem[3], 65'h0);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
