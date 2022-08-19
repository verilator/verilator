module t;

class T;
    function automatic void print_str(input string a_string);
        $display(a_string);
    endfunction
endclass


initial begin
    T t_c = new;
    t_c.print_str("print me");
    $write("*-* All Finished *-*\n");
    $finish;
end
endmodule
