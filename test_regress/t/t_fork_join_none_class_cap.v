// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

event evt1;

typedef enum {ENUM_VALUE} enum_t;

class Foo;
  int m_member;
  enum_t m_en;

  task do_something();
    fork
      #20 begin
        m_member++;
        $display("this's m_member: %0d  m_en: %s", m_member, m_en.name());
        if (m_member != 3)
          $stop;
        ->evt1;
      end
      #10 begin
        m_member++;
        bar(this);
      end
    join_none
  endtask

  static task bar(Foo foo);
    fork
      begin
        foo.m_member++;
        $display("foo's m_member: %0d  m_en: %s", foo.m_member, foo.m_en.name());
        if (foo.m_member != 2)
          $stop;
      end
    join_none
  endtask
endclass

module t();
  initial begin
    Foo foo;
    foo = new;
    foo.m_member = 0;
    foo.do_something();
  end

  always @(evt1) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
