// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  integer cycles;
  initial begin
    integer fd;
    fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/t_fourstate_fwrite_logger.log"}, "w");
    $fwrite(fd, "%0d\n", cycles);
    cycles++;
    $fwrite(fd, "%0d\n", cycles);
    cycles = 0;
    $fwrite(fd, "%0d\n", cycles);
    cycles++;
    $fwrite(fd, "%0d\n", cycles);
    $fclose(fd);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
