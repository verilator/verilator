module cnt (
    input clk,
    input rst
);
  logic q;
  always_ff @(posedge clk, posedge rst) begin
    if (rst) q <= 0;
    else begin
      $display("asd");
      q <= q + 1;
    end
  end
endmodule

module tb;
  // 1. Declare a non-local (module-level) variable
  int module_counter = 0;

  // 2. Export the SystemVerilog function so C can call it
  export "DPI-C" function sv_add_to_counter;

  // 3. Import the C function. 
  // The 'context' keyword is REQUIRED here because the C function 
  // will call an exported function that accesses instance-specific data.
  import "DPI-C" context task c_execute_test();

  // 4. Define the exported SystemVerilog function
  function void sv_add_to_counter(input int amount);
    // Writing to the non-local variable
    module_counter += amount;
    $display("[SV Time %0t] Exported function called! module_counter is now: %0d", $time,
             module_counter);
  endfunction
  logic clk = 0, rst = 0;
  cnt c (
      .clk,
      .rst
  );

  // 5. Run the test
  initial begin
    $display("[SV] Starting test. Initial module_counter: %0d", module_counter);

    // Pass control to C
    c_execute_test();

    $display("[SV] Test finished. Final module_counter: %0d", module_counter);
    rst = 1;
    #10 rst = 0;
    #10 clk = 1;
    #10 clk = 0;
    #10 clk = 1;
    $finish;
  end
endmodule
