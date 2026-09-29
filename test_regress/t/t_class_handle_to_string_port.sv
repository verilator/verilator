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
        // pinp is VarRef to 'seq' -> varp()->basicp() == nullptr -> crash
        c.f(seq);  // SEMI-ILLEGAL (class handle as string), but should be an error, not SIGSEGV
    end
endmodule
