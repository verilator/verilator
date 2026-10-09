// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class FixedSizePacket;
  rand int unsigned length;
  rand int data[];

  constraint contents {
    data.size() == 3;
    foreach (data[index]) data[index] < index;
  }
endclass

class LengthSizePacket;
  rand int unsigned length;
  rand int data[];

  constraint contents {
    data.size() == length;
    foreach (data[index]) data[index] < index;
  }
endclass

class DerivedSizePacket extends LengthSizePacket;
endclass

class SizeOnlyPacket;
  rand int length;
  rand int data[];
  constraint contents {data.size() == 3;}
endclass

class InlineSizePacket;
  rand int data[];
endclass

module t;
  initial begin
    automatic FixedSizePacket fsp = new;
    automatic LengthSizePacket lsp = new;
    automatic DerivedSizePacket dsp = new;
    automatic InlineSizePacket isp = new;
    automatic SizeOnlyPacket sop = new;
    automatic int res;

    res = fsp.randomize() with {
      length == 2;
      data[0] == -15;
    };
    `checkd(res, 1);
    `checkd(fsp.length, 2);
    `checkd(fsp.data.size(), 3);
    foreach (fsp.data[index]) if (fsp.data[index] >= index) $stop;
    `checkd(fsp.data[0], -15);

    res = fsp.randomize() with {foreach (data[index]) data[index] == 20;};
    `checkd(res, 0)

    res = lsp.randomize() with {length == 1;};
    `checkd(res, 1);
    `checkd(lsp.length, 1);
    `checkd(lsp.data.size(), 1);

    res = lsp.randomize() with {
      length % 3 == 0;
      data.size() == 9;
      data[5] == 2;
    };
    `checkd(res, 1);
    `checkd(lsp.length, 9);
    `checkd(lsp.data.size(), 9);

    foreach (lsp.data[index]) if (lsp.data[index] >= index) $stop;
    `checkd(lsp.data[5], 2);

    begin
      int prev_data  [6];
      bit difference;
      for (int size = 0; size < 6; ++size) begin
        res = lsp.randomize() with {length == local:: size;};
        `checkd(res, 1);
        `checkd(lsp.length, size);
        `checkd(lsp.data.size(), size);
        foreach (lsp.data[index]) begin
          if (lsp.data[index] >= index) $stop;
          difference |= index != size - 1 && lsp.data[index] != prev_data[index];
          prev_data[index] = lsp.data[index];
        end
      end
      `checkd(difference, 1);
    end

    res = dsp.randomize() with {length == 7;};
    `checkd(res, 1);
    `checkd(dsp.data.size(), 7);
    foreach (dsp.data[index]) if (dsp.data[index] >= index) $stop;

    for (int size = 1; size < 5; ++size) begin
      res = isp.randomize() with {
        data.size() == local:: size;
        foreach (data[index]) data[index] == index + 1;
      };
      `checkd(res, 1);
      `checkd(isp.data.size(), size);
      foreach (isp.data[index]) `checkd(isp.data[index], index + 1);
    end

    lsp.data = new[2];
    foreach (lsp.data[index]) lsp.data[index] = -1;
    lsp.data.rand_mode(0);
    res = lsp.randomize() with {length == 2;};
    `checkd(res, 1);
    `checkd(lsp.data.size(), 2);
    foreach (lsp.data[index]) `checkd(lsp.data[index], -1);
    res = lsp.randomize() with {length == 3;};
    `checkd(res, 0);
    `checkd(lsp.data.size(), 2);
    foreach (lsp.data[index]) `checkd(lsp.data[index], -1);

    res = sop.randomize() with {length == 2;};
    `checkd(res, 1);
    `checkd(sop.length, 2);
    `checkd(sop.data.size(), 3);

    res = sop.randomize() with {foreach (data[index]) data[index] == index + 1;};
    `checkd(res, 1);
    `checkd(sop.data.size(), 3);
    foreach (sop.data[index]) `checkd(sop.data[index], index + 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
