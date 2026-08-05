// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  task test_read(input integer f, output string l);
    automatic string line;
    automatic string buffer = "";
    automatic integer code;

    if (f == 0) $stop;
    while (1) begin
      code = $fgets(line, f);
      // Uncomment for issue #7976 workaround
      // $display("code %d => content: %s", code, line);
      buffer = {buffer, line};
      if (line == "") begin
        break;
      end
    end
    l = buffer;
  endtask

  task test_eof_tsk;
    automatic integer fd;
    automatic string test_file_name = "t/t_sys_fgets_loop.dat";
    automatic string output_line;
    // Open files
    fd = $fopen(test_file_name, "r");
    if (fd == 0) begin
      $display("ERROR ould not open file '%s' for reading aborting", test_file_name);
      $fatal(0);
    end

    while (!$feof(
        fd
    )) begin
      test_read(fd, output_line);
    end
    $fclose(fd);
  endtask

  initial begin
    test_eof_tsk;
  end

  initial begin
    #100;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
