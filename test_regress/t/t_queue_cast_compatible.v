// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Paul Swirhun.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,
               expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (  /*AUTOARG*/);

  // Byte types for string casting
  typedef byte unsigned byte_array_t[];
  typedef byte unsigned byte_queue_t[$];

  // Different element widths for queue <-> array casting
  typedef logic [7:0] byte_array2_t[];
  typedef logic [7:0] byte_queue2_t[$];
  typedef logic [15:0] word_array_t[];
  typedef logic [15:0] word_queue_t[$];
  typedef logic [23:0] word_odd_array_t[];
  typedef logic [23:0] word_odd_queue_t[$];
  typedef logic [31:0] dword_array_t[];
  typedef logic [31:0] dword_queue_t[$];
  typedef logic [55:0] dword_odd_array_t[];
  typedef logic [55:0] dword_odd_queue_t[$];
  typedef logic [63:0] qword_array_t[];
  typedef logic [63:0] qword_queue_t[$];
  typedef logic [119:0] odd_array_t[];
  typedef logic [119:0] odd_queue_t[$];
  typedef logic [127:0] dqword_array_t[];
  typedef logic [127:0] dqword_queue_t[$];

  initial begin
    static string str = "Hi";
    byte_array_t  arr;
    byte_queue_t  que;

    // Test string <-> byte array/queue casting
    $display("Testing string <-> byte array/queue casting");

    // String to dynamic array
    arr = byte_array_t'(str);
    `checkh(arr[0], 8'h48);
    `checkh(arr[1], 8'h69);

    // Dynamic array to string
    str = string'(arr);
    `checks(str, "Hi");

    // String to queue
    que = byte_queue_t'(str);
    `checkh(que[0], 8'h48);
    `checkh(que[1], 8'h69);

    // Queue to string
    str = string'(que);
    `checks(str, "Hi");

    // Test queue <-> array casting with same element width
    $display("Testing queue <-> array casting with same element width");

    begin
      byte_array2_t arr2;
      byte_queue2_t que2;

      // Initialize queue
      que2 = {8'h41, 8'h42, 8'h43};  // "ABC"

      // Queue to array
      arr2 = byte_array2_t'(que2);
      `checkh(arr2[0], 8'h41);
      `checkh(arr2[1], 8'h42);
      `checkh(arr2[2], 8'h43);

      // Array to queue
      que2 = byte_queue2_t'(arr2);
      `checkh(que2[0], 8'h41);
      `checkh(que2[1], 8'h42);
      `checkh(que2[2], 8'h43);
    end

    // Test with 16-bit elements
    begin
      word_array_t warr;
      word_queue_t wque;

      wque = {16'h1234, 16'h5678};
      warr = word_array_t'(wque);
      `checkh(warr[0], 16'h1234);
      `checkh(warr[1], 16'h5678);

      wque = word_queue_t'(warr);
      `checkh(wque[0], 16'h1234);
      `checkh(wque[1], 16'h5678);
    end

    // Test with 24-bit elements (non-32-bit-aligned)
    begin
      word_odd_array_t woarr;
      word_odd_queue_t woque;

      woque = {24'h123456, 24'hABCDEF};
      woarr = word_odd_array_t'(woque);
      `checkh(woarr[0], 24'h123456);
      `checkh(woarr[1], 24'hABCDEF);

      woque = word_odd_queue_t'(woarr);
      `checkh(woque[0], 24'h123456);
      `checkh(woque[1], 24'hABCDEF);
    end

    // Test with 32-bit elements
    begin
      dword_array_t dwarr;
      dword_queue_t dwque;

      dwque = {32'h12345678, 32'hABCDEF00};
      dwarr = dword_array_t'(dwque);
      `checkh(dwarr[0], 32'h12345678);
      `checkh(dwarr[1], 32'hABCDEF00);

      dwque = dword_queue_t'(dwarr);
      `checkh(dwque[0], 32'h12345678);
      `checkh(dwque[1], 32'hABCDEF00);
    end

    // Test with 56-bit elements (non-64-bit-aligned)
    begin
      dword_odd_array_t dwoarr;
      dword_odd_queue_t dwoque;

      dwoque = {56'h123456789ABCDE, 56'hFEDCBA09876543};
      dwoarr = dword_odd_array_t'(dwoque);
      `checkh(dwoarr[0], 56'h123456789ABCDE);
      `checkh(dwoarr[1], 56'hFEDCBA09876543);

      dwoque = dword_odd_queue_t'(dwoarr);
      `checkh(dwoque[0], 56'h123456789ABCDE);
      `checkh(dwoque[1], 56'hFEDCBA09876543);
    end

    // Test with 64-bit elements
    begin
      qword_array_t qwarr;
      qword_queue_t qwque;

      qwque = {64'h123456789ABCDEF0, 64'hFEDCBA0987654321};
      qwarr = qword_array_t'(qwque);
      `checkh(qwarr[0], 64'h123456789ABCDEF0);
      `checkh(qwarr[1], 64'hFEDCBA0987654321);

      qwque = qword_queue_t'(qwarr);
      `checkh(qwque[0], 64'h123456789ABCDEF0);
      `checkh(qwque[1], 64'hFEDCBA0987654321);
    end

    // Test with 128-bit elements
    begin
      dqword_array_t dqwarr;
      dqword_queue_t dqwque;

      dqwque = {128'h123456789ABCDEF0FEDCBA0987654321, 128'hAABBCCDDEEFF00112233445566778899};
      dqwarr = dqword_array_t'(dqwque);
      `checkh(dqwarr[0], 128'h123456789ABCDEF0FEDCBA0987654321);
      `checkh(dqwarr[1], 128'hAABBCCDDEEFF00112233445566778899);

      dqwque = dqword_queue_t'(dqwarr);
      `checkh(dqwque[0], 128'h123456789ABCDEF0FEDCBA0987654321);
      `checkh(dqwque[1], 128'hAABBCCDDEEFF00112233445566778899);
    end

    // Test with 120-bit elements (non-word-aligned)
    begin
      odd_array_t oddarr;
      odd_queue_t oddque;

      oddque = {120'h123456789ABCDEF0FEDCBA098765, 120'hAABBCCDDEEFF001122334455667};
      oddarr = odd_array_t'(oddque);
      `checkh(oddarr[0], 120'h123456789ABCDEF0FEDCBA098765);
      `checkh(oddarr[1], 120'hAABBCCDDEEFF001122334455667);

      oddque = odd_queue_t'(oddarr);
      `checkh(oddque[0], 120'h123456789ABCDEF0FEDCBA098765);
      `checkh(oddque[1], 120'hAABBCCDDEEFF001122334455667);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
