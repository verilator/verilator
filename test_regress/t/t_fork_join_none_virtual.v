// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

event evt1;

typedef enum {ENUM_VALUE} enum_t;

class Foo;
  int m_member;
  enum_t m_en;

  virtual task do_something();
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

class Subfoo extends Foo;
  virtual task do_something();#5;endtask
endclass

module t();
  initial begin
    Subfoo subfoo;
    Foo foo;
    subfoo = new;
    subfoo.do_something();
    foo = new;
    foo.m_member = 0;
    foo.do_something();
  end

  always @(evt1) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
