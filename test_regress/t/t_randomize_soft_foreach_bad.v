// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Cls1;
  rand int arr[10];
  constraint c_cls {
    soft foreach(arr[i]) arr[i] == i;
  }
endclass
