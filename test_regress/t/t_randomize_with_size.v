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

class DerivedOwnSizePacket extends LengthSizePacket;
  rand int extra[];
  constraint extra_contents {
    extra.size() == length + 1;
    foreach (extra[index]) extra[index] == index + 10;
  }
endclass

class FurtherDerivedSizePacket extends DerivedOwnSizePacket;
endclass

class MixedSizePacket;
  rand int data[];
  rand int extra[];
  constraint contents {data.size() == 3;}
endclass

class SizeOnlyPacket;
  rand int length;
  rand int data[];
  constraint contents {data.size() == 3;}
endclass

class DerivedSizeOnlyPacket extends SizeOnlyPacket;
endclass

class InlineSizePacket;
  rand int data[];
endclass

class QueueSizePacket;
  rand int unsigned length;
  rand bit [6:0] data[$];
  constraint contents {data.size() == length;}
endclass

module t;
  initial begin
    repeat (20) begin
      automatic FixedSizePacket fsp = new;
      automatic int res;

      res = fsp.randomize() with {
        length == 2;
        data[0] == -15;
      };
      `checkd(res, 1);
      `checkd(fsp.length, 2);
      `checkd(fsp.data.size(), 3);
      foreach (fsp.data[index]) `checkd(fsp.data[index] < index, 1);
      `checkd(fsp.data[0], -15);

      res = fsp.randomize() with {foreach (data[index]) data[index] == 20;};
      `checkd(res, 0);
    end

    repeat (20) begin
      automatic LengthSizePacket lsp = new;
      automatic int res;
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

      foreach (lsp.data[index]) `checkd(lsp.data[index] < index, 1);
      `checkd(lsp.data[5], 2);
    end

    repeat (20) begin
      automatic LengthSizePacket lsp = new;
      automatic int res;
      int prev_data[6];
      automatic bit difference = 0;
      for (int size = 0; size < 6; ++size) begin
        res = lsp.randomize() with {length == local:: size;};
        `checkd(res, 1);
        `checkd(lsp.length, size);
        `checkd(lsp.data.size(), size);
        foreach (lsp.data[index]) begin
          `checkd(lsp.data[index] < index, 1);
          difference |= index != size - 1 && lsp.data[index] != prev_data[index];
          prev_data[index] = lsp.data[index];
        end
      end
      `checkd(difference, 1);
    end

    repeat (20) begin
      automatic DerivedSizePacket dsp = new;
      automatic int res;
      res = dsp.randomize() with {length == 7;};
      `checkd(res, 1);
      `checkd(dsp.length, 7);
      `checkd(dsp.data.size(), 7);
      foreach (dsp.data[index]) `checkd(dsp.data[index] < index, 1);
    end

    repeat (20) begin
      automatic DerivedOwnSizePacket packet = new;
      int res;
      for (int size = 1; size < 5; ++size) begin
        res = packet.randomize() with {length == local:: size;};
        `checkd(res, 1);
        `checkd(packet.length, size);
        `checkd(packet.data.size(), size);
        foreach (packet.data[index]) `checkd(packet.data[index] < index, 1);
        `checkd(packet.extra.size(), size + 1);
        foreach (packet.extra[index]) `checkd(packet.extra[index], index + 10);
      end
    end

    repeat (20) begin
      automatic FurtherDerivedSizePacket packet = new;
      int res;
      for (int size = 1; size < 5; ++size) begin
        res = packet.randomize() with {length == local:: size;};
        `checkd(res, 1);
        `checkd(packet.length, size);
        `checkd(packet.data.size(), size);
        foreach (packet.data[index]) `checkd(packet.data[index] < index, 1);
        `checkd(packet.extra.size(), size + 1);
        foreach (packet.extra[index]) `checkd(packet.extra[index], index + 10);
      end
    end

    repeat (20) begin
      automatic InlineSizePacket isp = new;
      automatic int res;
      for (int size = 1; size < 5; ++size) begin
        res = isp.randomize() with {
          data.size() == local:: size;
          foreach (data[index]) data[index] == index + 1;
        };
        `checkd(res, 1);
        `checkd(isp.data.size(), size);
        foreach (isp.data[index]) `checkd(isp.data[index], index + 1);
      end
    end

    repeat (20) begin
      automatic MixedSizePacket packet = new;
      int res;
      for (int size = 1; size < 5; ++size) begin
        res = packet.randomize() with {
          extra.size() == local:: size;
          foreach (extra[index]) extra[index] == index + 1;
        };
        `checkd(res, 1);
        `checkd(packet.data.size(), 3);
        `checkd(packet.extra.size(), size);
        foreach (packet.extra[index]) `checkd(packet.extra[index], index + 1);
      end
    end

    repeat (20) begin
      automatic LengthSizePacket lsp = new;
      automatic int res;
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

    end

    repeat (20) begin
      automatic SizeOnlyPacket sop = new;
      automatic int res;
      sop.data = new[1];
      res = sop.randomize() with {length == 2;};
      `checkd(res, 1);
      `checkd(sop.length, 2);
      `checkd(sop.data.size(), 3);
    end

    repeat (20) begin
      automatic DerivedSizeOnlyPacket packet = new;
      automatic int res;
      packet.data = new[1];
      res = packet.randomize() with {length == 2;};
      `checkd(res, 1);
      `checkd(packet.length, 2);
      `checkd(packet.data.size(), 3);
    end

    repeat (20) begin
      automatic SizeOnlyPacket sop = new;
      automatic int res;
      res = sop.randomize() with {foreach (data[index]) data[index] == index + 1;};
      `checkd(res, 1);
      `checkd(sop.data.size(), 3);
      foreach (sop.data[index]) `checkd(sop.data[index], index + 1);
    end

    repeat (20) begin
      automatic QueueSizePacket packet = new;
      int res;
      for (int size = 0; size < 6; ++size) begin
        res = packet.randomize() with {
          length == local:: size;
          unique {data};
          foreach (data[index]) data[index] inside {[7'd123 : 7'd127]};
        };
        `checkd(res, 1);
        `checkd(packet.length, size);
        `checkd(packet.data.size(), size);
        foreach (packet.data[index]) begin
          `checkd(packet.data[index] inside {[7'd123 : 7'd127]}, 1);
          foreach (packet.data[other])
          if (index < other) `checkd(packet.data[index] != packet.data[other], 1);
        end
      end

      res = packet.randomize() with {
        length == 6;
        unique {data};
        foreach (data[index]) data[index] inside {[7'd123 : 7'd127]};
      };
      `checkd(res, 0);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
