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

   integer      cyc=0;
   reg [4095:0] crc;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[4094:0], crc[63]^crc[2]^crc[0]};  // not a good crc :)
      if (cyc==0) begin
         // Setup
         crc <= 4096'h9f51804b5275c7b6ab9907144a58649bb778f9718062fa5c336fcc9edcad7cf17aad0a656244017bb21d9f97f7c0c147b6fa7488bb9d5bb8d3635b20fba1deab597121c502b21f49b18da998852d29a6b2b649315a3323a31e7e5f41e9bbb7e44046467438f37694857b963250bdb137a922cfce2af1defd1f93db5aa167f316d751bb274bda96fdee5e2c6eb21886633246b165341f0594c27697b06b62b1ad05ebe3c08909a54272de651296dcdd3d1774fc432d22210d8f6afa50b02cf23336f8cc3a0a2ebfd1a3a60366a1b66ef346e0379116d68caa01279ac2772d1f3cd76d2cbbc68ada6f83ec2441b2679b405486df8aa734ea1729b40c3f82210e8e42823eb3fd6ca77ee19f285741c4e8bac1ab7855c3138e84b6da1d897bbe37faf2d0256ad2f7ff9e704a63d824c1e97bddce990cae1578f9537ae2328d0afd69ffb317cbcf859696736e45e5c628b44727557c535a7d02c07907f2dccd6a21ca9ae9e1dbb1a135a8ebc2e0aa8c7329b898d02896273defe21beaa348e11165b71c48cf1c09714942a5a2ddc2adcb6e42c0f630117ee21205677d5128e8efc18c9a6f82a8475541fd722cca2dd829b7e78fef89dbeab63ab7b849910eb4fe675656c4b42b9452c81a4ca6296190a81dc63e6adfaa31995d7dfe3438ee9df66488d6cf569380569ffe6e5ea313d23af6ff08d979af29374ee9aff1fa143df238a1;
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x%x%x%x\n",$time, cyc, crc[4095:3072], crc[2071:2048], crc[2047:1024], crc[1023:0]);
         $write("[%0t] cyc==%0d crc=%b%b%b%b\n",$time, cyc, crc[4095:3072], crc[2071:2048], crc[2047:1024], crc[1023:0]);
         //Unsupported: $write("[%0t] cyc==%0d crc=%x\n",$time, cyc, crc);
         if (crc != 4096'h2961926edde3e5c6018be970cdbf327b72b5f3c5eab42995891005eec8767e5fdf03051edbe9d222ee756ee34d8d6c83ee877aad65c487140ac87d26c636a66214b4a69acad924c568cc8e8c79f97d07a6eedf91011919d0e3cdda5215ee58c942f6c4dea48b3f38abc77bf47e4f6d6a859fcc5b5d46ec9d2f6a5bf7b978b1bac862198cc91ac594d07c165309da5ec1ad8ac6b417af8f0224269509cb79944a5b7374f45dd3f10cb48884363dabe942c0b3c8ccdbe330e828baff468e980d9a86d9bbcd1b80de445b5a32a8049e6b09dcb47cf35db4b2ef1a2b69be0fb09106c99e6d01521b7e2a9cd3a85ca6d030fe08843a390a08facff5b29dfb867ca15d0713a2eb06ade1570c4e3a12db687625eef8dfebcb4095ab4bdffe79c1298f609307a5ef773a6432b855e3e54deb88ca342bf5a7fecc5f2f3e165a59cdb9179718a2d11c9d55f14d69f40b01e41fcb7335a8872a6ba7876ec684d6a3af0b82aa31cca6e26340a2589cf7bf886faa8d23844596dc71233c7025c5250a968b770ab72db90b03d8c045fb8848159df544a3a3bf063269be0aa11d5507f5c8b328b760a6df9e3fbe276faad8eadee126443ad3f99d595b12d0ae514b20693298a58642a07718f9ab7ea8c66575f7f8d0e3ba77d992235b3d5a4e015a7ff9b97a8c4f48ebdbfc2365e6bca4dd3ba6bfc7e850f7c8e2842c717a1d85a977a033f564fc
             ) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
