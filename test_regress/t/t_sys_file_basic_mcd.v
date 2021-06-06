// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


module t;
`define STR(__s) `"__s`"

  task automatic fail(string s); begin
    $display({"FAIL! Reason: ", s});
    $stop;
  end endtask

  task automatic test1; begin
    int fd[30], fd_fail, fd_success, fd_close, tmp;
    for (int i = 0; i < 30; i++) begin
      // Attempt to allocate 30 MCD descriptors; returned descriptors
      // should fall within correct range: [1, 30].
      tmp  = $fopen($sformatf("%s/some_file%0d.dat", `STR(`TEST_OBJ_DIR), i));
      fd[i]  = tmp;
      if ((fd[i] == 0) || !$onehot(fd[i]))
        fail($sformatf("MCD descriptor out of range %d", fd[i]));
    end
    // Attempt to allocate another MCD descriptor when all should
    // be used. We expect this operation to fail and return the
    // invalid descriptor (0).
    fd_fail = $fopen($sformatf("%s/another_file.dat", `STR(`TEST_OBJ_DIR)));
    if (fd_fail != 0)
      fail("Able to allocate MCD descriptor when fully utilized.");
    // Return descriptor back to pool
    fd_close = fd[0];
    $fclose(fd_close);
    // Re-attempt MCD allocation; should pass at this point.
    fd_success = $fopen($sformatf("%s/yet_another_file.dat", `STR(`TEST_OBJ_DIR)));
    if (fd_success == 0)
      fail("Expect to have free descriptors at this point.");
    // Returned descriptor should have a value matching that which
    // had previously just been returned back to the pool.
    if (fd_success != fd[0])
      fail("Descriptor has incorrect value.");
    // Return all descriptors back to the pool.
    for (int i = 1; i < 30; i++) begin
      fd_close  = fd[i];
      $fclose(fd_close);
    end
  end endtask

  task automatic test2; begin
    // Validate basic MCD functionality.

    integer fd[3], fd_all, tmp;
    for (int i = 0; i < 3; i++) begin

      tmp  = $fopen($sformatf("%s/t_sys_file_basic_mcd_test2_%0d.dat", `STR(`TEST_OBJ_DIR), i));
      fd[i]  = tmp;
    end

    fd_all  = 0;
    for (int i = 0; i < 3; i++)
      fd_all  |= fd[i];

    $fwrite(fd_all, "Scotland is the greatest country.\n");
    $fwrite(fd_all, "All other countries are inferior.\n");
    $fwrite(fd_all, "Woe betide those to stand against the mighty Scottish nation.\n");
    $fclose(fd_all);
  end endtask

  task automatic test3; begin
    // Write some things to standard output.
    $fwrite(32'h8000_0001, "Sean Connery was the best Bond.\n");
  end endtask

  task automatic test4; begin
    int fd;
    // Wide filename
    fd = $fopen({`STR(`TEST_OBJ_DIR),
                 "/some_very_large_filename_that_no_one_would_ever_use_",
                 "except_to_purposefully_break_my_beautiful_code.dat"});
    if (fd == 0) fail("Long filename could not be opened.");
    $fclose(fd);
  end endtask

  task automatic test5; begin
    int fd_all;
    fd_all = $fopen({`STR(`TEST_OBJ_DIR), "/t_sys_file_basic_mcd_test5.dat"});
    if (fd_all == 0) fail("could not be opened.");
    fd_all |= 1;
    $fdisplay(fd_all, "To file and to stdout");
    $fclose(fd_all);
  end endtask

  initial begin

    // Test1: Validate file descriptor region.
    test1;

    // Test2: Validate basic MCD functionality.
    test2;

    // Test3: Validate explicit descriptor ID
    test3;

    // Test4: Validate filename lengths
    test4;

    // Test5: OR with stdout
    test5;

    $write("*-* All Finished *-*\n");
    $finish(0);  // Test arguments to finish

  end // initial begin

`undef STR
endmodule // t
