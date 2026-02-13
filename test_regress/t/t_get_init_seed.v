class my_c;
  rand bit [5:0] b1;

  function void post_randomize();
    $info ("Random value generated as: 0x%h", b1);
  endfunction : post_randomize

endclass : my_c

module tb ();
  int seed = 1;

  my_c my_c_0;

  initial begin
    my_c_0 = new();
    /* verilator lint_off WIDTHTRUNC */
    a1 : assert (my_c_0.randomize());
    #5;
    seed = $get_initial_random_seed();
    $display("get_initial_random_seed=%0d", seed);
    $write("*-* All Finished *-*\n");
    $finish(2);
  end

endmodule
