// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0


int evt_recv_cnt;
int new_evt_recv_cnt;

module t();

  class Foo;
    event evt1;

    task automatic send_evt();
      fork
        #10 begin ->evt1; end
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
      fork begin
        @evt1 $display("Received evt1");
        evt_recv_cnt++;
      end join_none
    endtask

  endclass

  initial begin
    Foo foo1;
    foo1 = new;

    evt_recv_cnt = 0;
    new_evt_recv_cnt = 0;

    for (int i = 0; i < 4; i++) begin
      foo1.wait_for_event();
      #10;
      foo1.send_evt();
      #90;
      $display("- end of iteration -");
      if (evt_recv_cnt != i + 1)
        $stop;
      if (new_evt_recv_cnt != i)
        $stop;
    end

    if (evt_recv_cnt != 4)
      $stop;
    if (new_evt_recv_cnt != 3)
      $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
