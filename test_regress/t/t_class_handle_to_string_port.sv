// DESCRIPTION: Verilator: segfault in V3Width processFTaskRefArgs
// varp->basicp() is nullptr for class-typed pin to string port

class Base;
endclass

class Caller;
  function void f(input string s);
    $display("%s", s);
  endfunction
endclass

module t;
  initial begin
    automatic Caller c = new;
    automatic Base seq = new;
    // Passing a class handle where a 'string' port is expected:
    c.f(seq);
  end
endmodule
