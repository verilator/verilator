// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2030 by Stephen Henry.
// SPDX-License-Identifier: CC0-1.0

module t;

  int fdin_bin, fdout_txt, fdout_bin;
`define STRINGIFY(x) `"x`"

`define checkh(gotv,expv) \
  do if ((gotv) !== (expv)) begin\
      $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv));\
   end while(0)

  //
  //
  task automatic test1; begin
    for (int i = 0; i < 256; i++) begin
      byte actual, expected;
      expected  = i[7:0];
      $fscanf(fdin_bin, "%u", actual);
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end

    for (int i = 0; i < 256; i++) begin
      shortint actual, expected;
      for (int j = 0; j < 2; j++)
        expected[(8 * j)+:8]  = i[7:0] + j[7:0];
      $fscanf(fdin_bin, "%u", actual);
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end

    for (int i = 0; i < 256; i++) begin
      int actual, expected;
      for (int j = 0; j < 4; j++)
        expected[(8 * j)+:8]  = i[7:0] + j[7:0];
      $fscanf(fdin_bin, "%u", actual);
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%u", actual);
    end

    for (int i = 0; i < 256; i++) begin
      longint actual, expected;
      for (int j = 0; j < 8; j++)
        expected[(8 * j)+:8]  = i[7:0] + j[7:0];
      $fscanf(fdin_bin, "%u", actual);
      `checkh(actual, expected);
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
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end

    for (int i = 0; i < 256; i++) begin
      shortint actual, expected;
      for (int j = 0; j < 2; j++)
        expected[(8 * j)+:8]  = i[7:0] + j[7:0];
      $fscanf(fdin_bin, "%z", actual);
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end

    for (int i = 0; i < 256; i++) begin
      int actual, expected;
      for (int j = 0; j < 4; j++)
        expected[(8 * j)+:8]  = i[7:0] + j[7:0];
      $fscanf(fdin_bin, "%z", actual);
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end

    for (int i = 0; i < 256; i++) begin
      longint actual, expected;
      for (int j = 0; j < 8; j++)
        expected[(8 * j)+:8]  = i[7:0] + j[7:0];
      $fscanf(fdin_bin, "%z", actual);
      `checkh(actual, expected);
      $fdisplay(fdout_txt, "%h", actual);
      $fwrite(fdout_bin, "%z", actual);
    end
  end endtask

  initial begin : main_PROC

    string filename;

    filename  = "t/t_sys_file_basic_uz.dat";
    fdin_bin  = $fopen(filename, "rb");

`ifdef IVERILOG
    filename  = $sformatf("%s/t_sys_file_basic_uz_test.log","obj_iv/t_sys_file_basic_uz");
`else
    filename  = $sformatf("%s/t_sys_file_basic_uz_test.log",`STRINGIFY(`TEST_OBJ_DIR));
`endif
    fdout_txt  = $fopen(filename, "w");

`ifdef IVERILOG
    filename  = $sformatf("%s/t_sys_file_basic_uz_test.bin","obj_iv/t_sys_file_basic_uz");
`else
    filename  = $sformatf("%s/t_sys_file_basic_uz_test.bin",`STRINGIFY(`TEST_OBJ_DIR));
`endif
    $display(filename);
    fdout_bin  = $fopen(filename, "wb");

    test1;
    test2;

    $fclose(fdin_bin);
    $fclose(fdout_txt);

    $write("*-* All Finished *-*\n");
    $finish(0);  // Test arguments to finish

  end // block: main_PROC

`undef STRINGIFY
endmodule // t
