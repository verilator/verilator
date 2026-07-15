// DESCRIPTION: Verilator: $finish propagation across timing resume boundaries
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class EventHolder;
  event ev;
endclass

package timing_lambda_pkg;
  int lambda_driver_after;
  int lambda_queue_after;
  int lambda_writer_after;
  int constructor_arg_after;
  int constructor_body_after;
  int constructor_outer_after;
  int constructor_values[8];

  class TimingArgument;
    task delay_finish();
      #1;
      $finish;
      constructor_arg_after++;
    endtask

    function int value();
      delay_finish();
      return 7;
    endfunction
  endclass

  class RefBox;
    function new(ref int value_arg);
      value_arg++;
      constructor_body_after++;
    endfunction
  endclass

  virtual class WriterIf;
    virtual function void write(input int value);
    endfunction
  endclass

  class BlockingWriter;
    task write(int value);
      #1;
      $finish;
      lambda_writer_after++;
    endtask
  endclass

  class WriterAdapter extends WriterIf;
    BlockingWriter writer;

    function new(BlockingWriter writer_arg);
      writer = writer_arg;
    endfunction

    function void write(input int value);
      writer.write(value);
    endfunction
  endclass

  class QueueLike;
    WriterIf sink;

    function bit try_get(output int value);
      value = 3;
      sink.write(value);
      lambda_queue_after++;
      return 1'b0;
    endfunction
  endclass

  class DriverLike;
    QueueLike queue;

    function void item_done();
      int value;
      if (queue.try_get(value) == 0) lambda_driver_after++;
      lambda_driver_after++;
    endfunction
  endclass
endpackage

module t;
  import timing_lambda_pkg::*;

  int begin_after;
  int delay_after;
  int event_after;
  int join_after;
  int join_any_after;
  int join_none_after;
  int leaf_after;
  int nested_after;
  int wait_fork_after;
  int wait_loop_after;
  bit wait_ready;

  EventHolder event_holder;

  task automatic leaf_finish(bit fire);
    if (fire) begin
      $finish;
      leaf_after++;
    end
  endtask

  task automatic nested_finish(bit fire);
    leaf_finish(fire);
    nested_after++;
  endtask

  initial begin
    string mode;
    event_holder = new;
    if (!$value$plusargs("MODE=%s", mode)) `stop;

    case (mode)
      "begin": begin
        fork
          begin
            #1;
            nested_finish(1'b1);
          end
          begin
            begin : lexical_block
              #1;
              begin_after++;
              nested_finish(1'b0);
            end
          end
        join_none
      end
      "constructor": begin
        TimingArgument source;
        RefBox box;

        source = new();
        box = new(constructor_values[source.value()]);
        constructor_outer_after++;
      end
      "join": begin
        fork
          begin
            #1;
            nested_finish(1'b1);
          end
        join
        join_after++;
        nested_finish(1'b0);
      end
      "join_any": begin
        fork
          begin
            #10;
            nested_finish(1'b0);
          end
          begin
            #1;
            nested_finish(1'b1);
          end
        join_any
        join_any_after++;
        nested_finish(1'b0);
      end
      "join_none": begin
        fork
          begin
            #0;
            nested_finish(1'b1);
          end
          begin
            #0;
            join_none_after++;
            nested_finish(1'b0);
          end
        join_none
      end
      "wait_fork": begin
        fork
          begin
            #1;
            nested_finish(1'b1);
          end
        join_none
        wait fork;
        wait_fork_after++;
        nested_finish(1'b0);
      end
      "delay": begin
        fork
          begin
            #1;
            nested_finish(1'b1);
          end
          begin
            #1;
            delay_after++;
            nested_finish(1'b0);
          end
        join_none
      end
      "event": begin
        fork
          begin
            @event_holder.ev;
            nested_finish(1'b1);
          end
          begin
            @event_holder.ev;
            event_after++;
            nested_finish(1'b0);
          end
          begin
            #1;
            ->event_holder.ev;
          end
        join_none
      end
      "wait_loop": begin
        fork
          begin
            wait (wait_ready);
            nested_finish(1'b1);
          end
          begin
            wait (wait_ready);
            wait_loop_after++;
            nested_finish(1'b0);
          end
          begin
            #1;
            wait_ready = 1'b1;
          end
        join_none
      end
      "lambda": begin
        BlockingWriter writer;
        WriterAdapter adapter;
        QueueLike queue;
        DriverLike driver;

        writer = new();
        adapter = new(writer);
        queue = new();
        queue.sink = adapter;
        driver = new();
        driver.queue = queue;
        driver.item_done();
      end
      default: `stop;
    endcase

    #100;
    `stop;
  end

  final begin
    `checkd(begin_after, 0);
    `checkd(constructor_arg_after, 0);
    `checkd(constructor_body_after, 0);
    `checkd(constructor_outer_after, 0);
    `checkd(delay_after, 0);
    `checkd(event_after, 0);
    `checkd(join_after, 0);
    `checkd(join_any_after, 0);
    `checkd(join_none_after, 0);
    `checkd(lambda_driver_after, 0);
    `checkd(lambda_queue_after, 0);
    `checkd(lambda_writer_after, 0);
    `checkd(leaf_after, 0);
    `checkd(nested_after, 0);
    `checkd(wait_fork_after, 0);
    `checkd(wait_loop_after, 0);
    $write("*-* All Finished *-*\n");
  end
endmodule
