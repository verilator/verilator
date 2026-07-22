// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop;
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module test;
  mailbox #(int) mbox;
  int seen_10 = 0;
  int seen_30 = 0;

  task automatic check_mbox_item(input int item);
    #0;
    if (item == 10) begin
      seen_10++;
    end
    else if (item == 30) begin
      seen_30++;
    end
    else begin
      $write("%%Error: unexpected item '%0d'\n", item);
      `stop;
    end
  endtask

  class driver;
    string names[string];
    int seen_a = 0;
    int seen_b = 0;

    task automatic check_name(input string name);
      #0;
      if (name == "a") begin
        seen_a++;
      end
      else if (name == "b") begin
        seen_b++;
      end
      else begin
        $write("%%Error: unexpected name '%0s'\n", name);
        `stop;
      end
    endtask

    task automatic make_name(input bit pick_b, output string name);
      name = pick_b ? "b" : "a";
      #0;
    endtask

    task automatic append_name(inout string name);
      // verilator no_inline_task
      #0;
      name = {name, "_done"};
    endtask

    task automatic check_arg_capture();
      names["a"] = "alpha";
      names["b"] = "bravo";

      foreach (names[name]) begin
        fork
          check_name(name);
        join_none
      end

      wait fork;

      `checkd(seen_a, 1);
      `checkd(seen_b, 1);
    endtask

    task automatic check_local_lifetime();
      seen_a = 0;
      seen_b = 0;

      for (int i = 0; i < 2; ++i) begin
        automatic bit pick_b = i[0];
        fork
          begin
            string name;
            name = pick_b ? "b" : "a";
            #0;
            check_name(name);
          end
        join_none
      end

      wait fork;

      `checkd(seen_a, 1);
      `checkd(seen_b, 1);
    endtask

    task automatic check_output_capture();
      seen_a = 0;
      seen_b = 0;

      for (int i = 0; i < 2; ++i) begin
        automatic bit pick_b = i[0];
        fork
          begin
            string name;
            make_name(pick_b, name);
            #0;
            check_name(name);
          end
        join_none
      end

      wait fork;

      `checkd(seen_a, 1);
      `checkd(seen_b, 1);
    endtask

    task automatic check_inout_capture();
      seen_a = 0;
      seen_b = 0;

      for (int i = 0; i < 2; ++i) begin
        automatic bit pick_b = i[0];
        fork
          begin
            string name = pick_b ? "b" : "a";
            append_name(name);
            #0;
            if (name == "a_done") begin
              seen_a++;
            end
            else if (name == "b_done") begin
              seen_b++;
            end
            else begin
              $write("%%Error: unexpected inout name '%0s'\n", name);
              `stop;
            end
          end
        join_none
      end

      wait fork;

      `checkd(seen_a, 1);
      `checkd(seen_b, 1);
    endtask

    task automatic run();
      check_arg_capture();
      check_local_lifetime();
      check_output_capture();
      check_inout_capture();
    endtask
  endclass

  initial begin
    driver drv;

    mbox = new();
    mbox.put(10);
    mbox.put(30);

    repeat (2) begin
      automatic int item;
      mbox.get(item);
      fork
        check_mbox_item(item);
      join_none
    end

    wait fork;

    `checkd(seen_10, 1);
    `checkd(seen_30, 1);

    drv = new;
    drv.run();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
