// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 by David Harris.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
// verilog_format: on

module t;

  int fd, code;
  string line;
  int siglines;

  localparam SIGNATURESIZE = 5000000;
  logic [31:0] sig32[0:SIGNATURESIZE];
  logic [31:0] parsed;
  string signame;

  initial begin
    signame = "t/t_sys_file_scan_delay.dat";

    fd = $fopen(signame, "r");
    siglines = 0;
    if (fd == 0) $display("Unable to read %s", signame);
    else begin
      $display("Read %s", signame);
      while (!$feof(
          fd
      )) begin
        code = $fgets(line, fd);
        if (code != 0) begin
          if (line.len() > 1) begin
            if ($sscanf(line, "%x", sig32[siglines]) != 0) begin
              $display("sig32[%1d] = %x   line: ", siglines, sig32[siglines], line);
              siglines = siglines + 1;  // increment if line is not blank
            end
          end
        end
      end
      $fclose(fd);
    end

    `checkh(sig32[0], 32'h10);
    `checkh(sig32[1], 32'h11);
    `checkh(sig32[2], 32'h12);
    $display("*-* All Finished *-*");
    $finish;
  end

endmodule
