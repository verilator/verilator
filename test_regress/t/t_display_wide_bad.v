// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [4095:0] crc;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[4094:0], crc[63] ^ crc[2] ^ crc[0]};  // not a good crc :)
      if (cyc==0) begin
         // Setup
         crc <= 4096'h9f51804b5275c7b6ab9907144a58649bb778f9718062fa5c336fcc9edcad7cf17aad0a656244017bb21d9f97f7c0c147b6fa7488bb9d5bb8d3635b20fba1deab597121c502b21f49b18da998852d29a6b2b649315a3323a31e7e5f41e9bbb7e44046467438f37694857b963250bdb137a922cfce2af1defd1f93db5aa167f316d751bb274bda96fdee5e2c6eb21886633246b165341f0594c27697b06b62b1ad05ebe3c08909a54272de651296dcdd3d1774fc432d22210d8f6afa50b02cf23336f8cc3a0a2ebfd1a3a60366a1b66ef346e0379116d68caa01279ac2772d1f3cd76d2cbbc68ada6f83ec2441b2679b405486df8aa734ea1729b40c3f82210e8e42823eb3fd6ca77ee19f285741c4e8bac1ab7855c3138e84b6da1d897bbe37faf2d0256ad2f7ff9e704a63d824c1e97bddce990cae1578f9537ae2328d0afd69ffb317cbcf859696736e45e5c628b44727557c535a7d02c07907f2dccd6a21ca9ae9e1dbb1a135a8ebc2e0aa8c7329b898d02896273defe21beaa348e11165b71c48cf1c09714942a5a2ddc2adcb6e42c0f630117ee21205677d5128e8efc18c9a6f82a8475541fd722cca2dd829b7e78fef89dbeab63ab7b849910eb4fe675656c4b42b9452c81a4ca6296190a81dc63e6adfaa31995d7dfe3438ee9df66488d6cf569380569ffe6e5ea313d23af6ff08d979af29374ee9aff1fa143df238a1;
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%d\n", $time, cyc, {crc, crc, crc, crc});  // Too wide
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
