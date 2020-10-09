`define PREFIX_        my_prefix_
`define SUFFIX          my_suffix
`define PREFIX_SUFFIX   my_prefix_suffix
`define name1           `PREFIX``_```SUFFIX
`define name2(p,s)      p``_``s
`define name3(p)        ```p``_SUFFIX
`define stringify(text) `"text`"

module t();
   initial begin
      // Another simulator gives:
      //  `PREFIX_my_suffix
      //  `name2(`PREFIX, my_suffix)
      //  `name3(PREFIX)
      $display(`stringify(`name1));
      $display(`stringify(`name2(`PREFIX, `SUFFIX)));
      $display(`stringify(`name3(PREFIX)));
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
