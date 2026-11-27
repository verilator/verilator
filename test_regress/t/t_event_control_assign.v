// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

int evt_recv_cnt;
int new_evt_recv_cnt;

module t;

  class Foo;
    event evt1;

    task check_dynamic_array();
      event events[];
      bit woke;
      events = new[2];
      `checkd(events[0] == events[1], 0);
      fork
        begin
          @(events[0]);
          woke = 1;
        end
      join_none
      #1 ->events[1];
      #1 `checkd(woke, 0);
      ->events[0];
      #1 `checkd(woke, 1);
    endtask

    task assign_event(input event source_event, output event destination_event);
      destination_event = source_event;
    endtask

    task check_queue();
      event queue_events[$][2];
      assign_event(evt1, queue_events[queue_events.size()][0]);
      assign_event(evt1, queue_events[queue_events.size()][0]);
      `checkd(queue_events[0][1] == queue_events[1][1], 0);
    endtask

    task check_associative_array();
      event events[int][2];
      events[0][0] = evt1;
      events[1][0] = evt1;
      `checkd(events[0][1] == events[1][1], 0);
      // New entries of an explicit default are merged with it
      events = '{default: '{evt1, evt1}};
      events[0][0] = evt1;
      `checkd(events[0][1] == evt1, 1);
    endtask

    task automatic send_evt();
      fork
        #10 begin
          ->evt1;
        end
        begin
          event new_event;
          #20;
          // This should cause an event merge but for now we don't support that.
          evt1 = new_event;
        end
        #30 begin
          @evt1 $display("Received a new event");
          new_evt_recv_cnt++;
        end
      join_none
    endtask

    task wait_for_event();
      fork
        begin
          @evt1 $display("Received evt1");
          evt_recv_cnt++;
        end
      join_none
    endtask

  endclass

  initial begin
    Foo foo1;
    foo1 = new;
    foo1.check_dynamic_array();
    foo1.check_queue();
    foo1.check_associative_array();

    evt_recv_cnt = 0;
    new_evt_recv_cnt = 0;

    for (int i = 0; i < 4; i++) begin
      foo1.wait_for_event();
      #10;
      foo1.send_evt();
      #90;
      $display("- end of iteration -");
      if (evt_recv_cnt != i + 1) $stop;
      if (new_evt_recv_cnt != i) $stop;
    end

    if (evt_recv_cnt != 4) $stop;
    if (new_evt_recv_cnt != 3) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
