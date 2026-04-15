// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  integer cycles;
  initial begin
    integer fd;
    fd = $fopen("/tmp/does-not-exist.txt");
    $fwrite(fd, "%0d", cycles);
    $fclose(fd);
  end
endmodule
