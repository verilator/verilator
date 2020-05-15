// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2030 by Stephen Henry.
// SPDX-License-Identifier: CC0-1.0

module t;

  int fdin_bin, fdout_txt, fdout_bin;
`define STRINGIFY(x) `"x`"

  //
  //
  task automatic error(string msg); begin
    $display({"FAIL! Reason: ", msg});
    $stop;
  end endtask

  //
  //
  task automatic test1; begin
    for (int i = 0; i < 256; i++) begin
      byte actual, expected;
      expected  = i[7:0];
      $fscanf(fdin_bin, "%u", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end

    for (int i = 0; i < 256; i++) begin
      shortint actual, expected;
      expected  = {2{i[7:0]}};
      $fscanf(fdin_bin, "%u", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end

    for (int i = 0; i < 256; i++) begin
      int actual, expected;
      expected  = {4{i[7:0]}};
      $fscanf(fdin_bin, "%u", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end

    for (int i = 0; i < 256; i++) begin
      longint actual, expected;
      expected  = {8{i[7:0]}};
      $fscanf(fdin_bin, "%u", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end
  end endtask

  //
  //
  task automatic test2; begin
    for (int i = 0; i < 256; i++) begin
      byte actual, expected;
      expected  = i[7:0];
      $fscanf(fdin_bin, "%z", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end

    for (int i = 0; i < 256; i++) begin
      shortint actual, expected;
      expected  = {2{i[7:0]}};
      $fscanf(fdin_bin, "%z", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end

    for (int i = 0; i < 256; i++) begin
      int actual, expected;
      expected  = {4{i[7:0]}};
      $fscanf(fdin_bin, "%z", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end

    for (int i = 0; i < 256; i++) begin
      longint actual, expected;
      expected  = {8{i[7:0]}};
      $fscanf(fdin_bin, "%z", actual);
      if (actual != expected)
        error($sformatf("Expected: %h Got: %h", expected, actual));
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end
  end endtask

  initial begin : main_PROC

    string filename;

    filename  = "t/t_sys_file_basic_uz.dat";
    fdin_bin  = $fopen(filename, "rb");
    if (fdin_bin == 0) error($sformatf("Failed to open file: %s", filename));

    filename   = $sformatf("%s/t_sys_file_basic_uz_test.log",`STRINGIFY(`TEST_OBJ_DIR));
    fdout_txt  = $fopen(filename, "w");
    if (fdout_txt == 0) error($sformatf("Failed to open file: %s", filename));

    filename   = $sformatf("%s/t_sys_file_basic_uz_test.bin",`STRINGIFY(`TEST_OBJ_DIR));
    fdout_bin  = $fopen(filename, "wb");
    if (fdout_bin == 0) error($sformatf("Failed to open file: %s", filename));

    test1;
    test2;

    $fclose(fdin_bin);
    $fclose(fdout_txt);

    $write("*-* All Finished *-*\n");
    $finish(0);  // Test arguments to finish

  end // block: main_PROC

`undef STRINGIFY
endmodule // t
