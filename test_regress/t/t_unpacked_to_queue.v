// DESCRIPTION: Verilator: Converting fixed-size arrays, queues and dynamic arrays
// in assignments and function arguments
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop()
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class check #(
    parameter WIDTH = 8
);
  static function automatic void check_array(int n, logic [WIDTH-1:0] array[]);
    `checkd(array.size(), n);
    for (int r = 0; r < n; r++) begin
      `checkh(array[r], WIDTH'(r))
    end
  endfunction

  static function automatic void check_string(int n, string array[]);
    `checkd(array.size(), n);
    for (int r = 0; r < n; r++) begin
      `checks(array[r], "test")
    end
  endfunction
endclass

class queue_item;
  int value;

  function new(int value);
    this.value = value;
  endfunction
endclass

module test ();

  localparam NUM_ELEMS = 4;

  typedef string array_s_t[NUM_ELEMS];
  typedef logic [7:0] array_8_t[NUM_ELEMS];
  typedef logic [15:0] array_16_t[NUM_ELEMS];
  typedef logic [31:0] array_32_t[NUM_ELEMS];
  typedef logic [63:0] array_64_t[NUM_ELEMS];
  typedef logic [95:0] array_96_t[NUM_ELEMS];

  typedef string queue_s_t[$];
  typedef logic [7:0] queue_8_t[$];
  typedef logic [15:0] queue_16_t[$];
  typedef logic [31:0] queue_32_t[$];
  typedef logic [63:0] queue_64_t[$];
  typedef logic [95:0] queue_96_t[$];

  array_s_t array_s;
  array_8_t array_8;
  array_16_t array_16;
  array_32_t array_32;
  array_64_t array_64;
  array_96_t array_96;

  queue_s_t queue_s;
  queue_8_t queue_8;
  queue_16_t queue_16;
  queue_32_t queue_32;
  queue_64_t queue_64;
  queue_96_t queue_96;

  function automatic bit [63:0] checked_word(bit [63:0] queued[$], bit [63:0] dynamic_words[],
                                             int index);
    `checkd(queued.size(), 3);
    `checkd(dynamic_words.size(), 3);
    `checkh(queued[index], dynamic_words[index]);
    return queued[index];
  endfunction

  function automatic void make_nested(output int values[$][4:6][$], input int seed);
    // verilator no_inline_task
    int row[4:6][$];
    values = '{};
    for (int i = 0; i < 2; ++i) begin
      foreach (row[j]) row[j] = '{seed + 10 * i + j};
      values.push_back(row);
    end
  endfunction

  function automatic void update_nested(inout int values[$][4:6][$]);
    // verilator no_inline_task
    foreach (values[i, j]) values[i][j].push_back(values[i][j][0] + 37);
  endfunction

  function automatic void make_items(output queue_item items[$], input int value);
    queue_item item = new(value);
    items = '{item};
  endfunction

  function automatic void replace_item(inout queue_item items[$]);
    items[0] = new(items[0].value + 1);
  endfunction

  initial begin
    for (int i = 0; i < NUM_ELEMS; i++) begin
      array_s[i] = "test";
      array_8[i] = 8'(i);
      array_16[i] = 16'(i);
      array_32[i] = 32'(i);
      array_64[i] = 64'(i);
      array_96[i] = 96'(i);
      queue_s.push_back("test");
      queue_8.push_back(8'(i));
      queue_16.push_back(16'(i));
      queue_32.push_back(32'(i));
      queue_64.push_back(64'(i));
      queue_96.push_back(96'(i));
    end

    check#(1)::check_string(NUM_ELEMS, array_s);
    check#(8)::check_array(NUM_ELEMS, array_8);
    check#(16)::check_array(NUM_ELEMS, array_16);
    check#(32)::check_array(NUM_ELEMS, array_32);
    check#(64)::check_array(NUM_ELEMS, array_64);
    check#(96)::check_array(NUM_ELEMS, array_96);

    queue_s = array_s;
    queue_8 = array_8;
    queue_16 = array_16;
    queue_32 = array_32;
    queue_64 = array_64;
    queue_96 = array_96;

    check#(1)::check_string(NUM_ELEMS, queue_s);
    check#(8)::check_array(NUM_ELEMS, queue_8);
    check#(16)::check_array(NUM_ELEMS, queue_16);
    check#(32)::check_array(NUM_ELEMS, queue_32);
    check#(64)::check_array(NUM_ELEMS, queue_64);
    check#(96)::check_array(NUM_ELEMS, queue_96);

    begin
      bit [63:0] preload[3];
      bit [63:0] alternate[3];
      bit [63:0] ascending[1:3];
      bit [63:0] descending[3:1];
      bit [63:0] assigned[$];
      bit [63:0] dynamic_words[];
      automatic bit select_first = 1'($urandom);
      repeat (3) begin
        foreach (preload[i]) begin
          preload[i] = {32'h81234567, $urandom};
          alternate[i] = ~preload[i];
          ascending[i+1] = preload[i];
          descending[3-i] = preload[i];
        end
        assigned = preload;
        foreach (preload[i]) `checkh(checked_word(preload, assigned, i), preload[i]);
        assigned[0] = 0;
        `checkh(preload[0][63:32], 32'h81234567);
        assigned = ascending;
        foreach (preload[i]) `checkh(checked_word(ascending, assigned, i), preload[i]);
        assigned = descending;
        foreach (preload[i]) `checkh(checked_word(descending, assigned, i), preload[i]);
        repeat (2) begin
          select_first = !select_first;
          assigned = select_first ? preload : alternate;
          dynamic_words = select_first ? preload : alternate;
          foreach (preload[i]) begin
            `checkh(checked_word(assigned, dynamic_words, i),
                    select_first ? preload[i] : alternate[i]);
            `checkh(checked_word(
                    select_first ? preload : alternate, select_first ? preload : alternate, i),
                    select_first ? preload[i] : alternate[i]);
          end
        end
      end
    end

    begin
      typedef logic [64:0] word_t;
      typedef word_t fixed_words_t[3:1];
      fixed_words_t preload;
      word_t assigned[$:2];
      foreach (preload[i]) preload[i] = {1'b1, 32'habcdef01, $urandom};
      assigned = preload;
      `checkd(assigned.size(), 3);
      foreach (preload[i]) `checkh(assigned[3-i], preload[i]);
    end

    begin
      typedef bit [62:0] word_t;
      typedef word_t row_t[6:4];
      typedef word_t ordered_row_t[4:6];
      row_t ascending[1:2];
      row_t descending[2:1];
      ordered_row_t reversed[$];
      ordered_row_t dynamic_words[];
      row_t matching[$];
      foreach (ascending[i, j]) begin
        ascending[i][j] = {1'b1, 30'($urandom), $urandom};
        descending[3-i][j] = ~ascending[i][j];
      end
      reversed = ascending;
      foreach (ascending[i, j]) `checkh(reversed[i-1][10-j], ascending[i][j]);
      reversed = descending;
      foreach (ascending[i, j]) `checkh(reversed[i-1][10-j], ~ascending[i][j]);
      dynamic_words = ascending;
      foreach (ascending[i, j]) `checkh(dynamic_words[i-1][10-j], ascending[i][j]);
      matching = descending;
      foreach (ascending[i, j]) `checkh(matching[i-1][j], ~ascending[i][j]);
    end

    begin
      int preload[2:1][6:4][$];
      automatic int seed = int'($urandom_range(1, 10000));
      make_nested(preload, seed);
      for (int size = 1; size <= 2; ++size) begin
        foreach (preload[i, j]) `checkd(preload[i][j].size(), size);
        foreach (preload[i, j, k]) `checkd(preload[i][j][k], seed + 10 * (2 - i) + 10 - j + 37 * k);
        if (size == 1) update_nested(preload);
      end
    end

    begin
      queue_item preload[1];
      queue_item previous;
      automatic int value = int'($urandom_range(1, 10000));
      make_items(preload, value);
      `checkd(preload[0] != null, 1'b1);
      `checkd(preload[0].value, value);
      previous = preload[0];
      replace_item(preload);
      `checkd(preload[0].value, value + 1);
      `checkd(previous.value, value);
    end

    $display("All checks passed");
    $finish();
  end
endmodule
