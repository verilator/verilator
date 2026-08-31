// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(parameter int SIZE = 4);

  // verilator lint_off UNDRIVEN
  // verilator lint_off UNUSEDSIGNAL

  reg i;
  wire I;

  import pkg::*;

  // Parameters and localparams: should not warn
  localparam int WIDTH = 8;
  logic [WIDTH-1:0] width;
  logic [WIDTH-1:0] reg_ctrl = REG_CTRL;
  logic [SIZE-1:0] size;

  // Genvar: should not warn
  logic genvar_name;
  genvar GENVAR_NAME;
  generate
    for (GENVAR_NAME = 0; GENVAR_NAME < 1; GENVAR_NAME++) begin : gen_loop
      logic unused_loop;
    end
  endgenerate

  // Typedef: should not warn
  logic typedef_name;
  typedef logic TYPEDEF_NAME;

  // Enum item: should not warn
  logic enum_item;
  typedef enum logic {ENUM_ITEM} enum_t;

  // Struct member: should not warn
  typedef struct packed {logic member_name; logic MEMBER_NAME;} memb_t;
  memb_t memb;

  // Property and sequence: should not warn
  logic prop_name, seq_name;
  property PROP_NAME; @(posedge i) prop_name; endproperty
  sequence SEQ_NAME; @(posedge i) seq_name; endsequence

  // Clocking block: should not warn
  logic clock_name;
  clocking CLOCK_NAME @(posedge i); input clock_name; endclocking

  // Modport: should not warn
  Ifc ifc ();

  // Randsequence production: should not warn
  logic rs_name;
  initial begin
    randsequence (rs_main)
      rs_main : rs_prod RS_PROD;
      rs_prod : {
        rs_name = 1'b0;
      };
      RS_PROD : {
        rs_name = 1'b0;
      };
    endsequence
  end

  // All ordered crosses of {var, net, genblock, begin, fork, task, function,
  // instance}: should warn

  // var/var
  logic var_var;
  logic VAR_VAR;

  // var/net
  logic var_net;
  wire VAR_NET;

  // var/genblock
  logic var_genblock;
  if (1) begin : VAR_GENBLOCK
  end

  // var/begin
  logic var_begin;
  initial begin : VAR_BEGIN
  end

  // var/fork
  logic var_fork;
  initial fork : VAR_FORK
  join

  // var/task
  logic var_task;
  task automatic VAR_TASK(); endtask

  // var/function
  logic var_function;
  function automatic bit VAR_FUNCTION(); return 1'b0; endfunction

  // var/instance
  logic var_instance;
  sub VAR_INSTANCE ();

  // net/var
  wire net_var;
  logic NET_VAR;

  // net/net
  wire net_net;
  wire NET_NET;

  // net/genblock
  wire net_genblock;
  if (1) begin : NET_GENBLOCK
  end

  // net/begin
  wire net_begin;
  initial begin : NET_BEGIN
  end

  // net/fork
  wire net_fork;
  initial fork : NET_FORK
  join

  // net/task
  wire net_task;
  task automatic NET_TASK(); endtask

  // net/function
  wire net_function;
  function automatic bit NET_FUNCTION(); return 1'b0; endfunction

  // net/instance
  wire net_instance;
  sub NET_INSTANCE ();

  // genblock/var
  if (1) begin : genblock_var
  end
  logic GENBLOCK_VAR;

  // genblock/net
  if (1) begin : genblock_net
  end
  wire GENBLOCK_NET;

  // genblock/genblock
  if (1) begin : genblock_genblock
  end
  if (1) begin : GENBLOCK_GENBLOCK
  end

  // genblock/begin
  if (1) begin : genblock_begin
  end
  initial begin : GENBLOCK_BEGIN
  end

  // genblock/fork
  if (1) begin : genblock_fork
  end
  initial fork : GENBLOCK_FORK
  join

  // genblock/task
  if (1) begin : genblock_task
  end
  task automatic GENBLOCK_TASK(); endtask

  // genblock/function
  if (1) begin : genblock_function
  end
  function automatic bit GENBLOCK_FUNCTION(); return 1'b0; endfunction

  // genblock/instance
  if (1) begin : genblock_instance
  end
  sub GENBLOCK_INSTANCE ();

  // begin/var
  initial begin : begin_var
  end
  logic BEGIN_VAR;

  // begin/net
  initial begin : begin_net
  end
  wire BEGIN_NET;

  // begin/genblock
  initial begin : begin_genblock
  end
  if (1) begin : BEGIN_GENBLOCK
  end

  // begin/begin
  initial begin : begin_begin
  end
  initial begin : BEGIN_BEGIN
  end

  // begin/fork
  initial begin : begin_fork
  end
  initial fork : BEGIN_FORK
  join

  // begin/task
  initial begin : begin_task
  end
  task automatic BEGIN_TASK(); endtask

  // begin/function
  initial begin : begin_function
  end
  function automatic bit BEGIN_FUNCTION(); return 1'b0; endfunction

  // begin/instance
  initial begin : begin_instance
  end
  sub BEGIN_INSTANCE ();

  // fork/var
  initial fork : fork_var
  join
  logic FORK_VAR;

  // fork/net
  initial fork : fork_net
  join
  wire FORK_NET;

  // fork/genblock
  initial fork : fork_genblock
  join
  if (1) begin : FORK_GENBLOCK
  end

  // fork/begin
  initial fork : fork_begin
  join
  initial begin : FORK_BEGIN
  end

  // fork/fork
  initial fork : fork_fork
  join
  initial fork : FORK_FORK
  join

  // fork/task
  initial fork : fork_task
  join
  task automatic FORK_TASK(); endtask

  // fork/function
  initial fork : fork_function
  join
  function automatic bit FORK_FUNCTION(); return 1'b0; endfunction

  // fork/instance
  initial fork : fork_instance
  join
  sub FORK_INSTANCE ();

  // task/var
  task automatic task_var(); endtask
  logic TASK_VAR;

  // task/net
  task automatic task_net(); endtask
  wire TASK_NET;

  // task/genblock
  task automatic task_genblock(); endtask
  if (1) begin : TASK_GENBLOCK
  end

  // task/begin
  task automatic task_begin(); endtask
  initial begin : TASK_BEGIN
  end

  // task/fork
  task automatic task_fork(); endtask
  initial fork : TASK_FORK
  join

  // task/task
  task automatic task_task(); endtask
  task automatic TASK_TASK(); endtask

  // task/function
  task automatic task_function(); endtask
  function automatic bit TASK_FUNCTION(); return 1'b0; endfunction

  // task/instance
  task automatic task_instance(); endtask
  sub TASK_INSTANCE ();

  // function/var
  function automatic bit function_var(); return 1'b0; endfunction
  logic FUNCTION_VAR;

  // function/net
  function automatic bit function_net(); return 1'b0; endfunction
  wire FUNCTION_NET;

  // function/genblock
  function automatic bit function_genblock(); return 1'b0; endfunction
  if (1) begin : FUNCTION_GENBLOCK
  end

  // function/begin
  function automatic bit function_begin(); return 1'b0; endfunction
  initial begin : FUNCTION_BEGIN
  end

  // function/fork
  function automatic bit function_fork(); return 1'b0; endfunction
  initial fork : FUNCTION_FORK
  join

  // function/task
  function automatic bit function_task(); return 1'b0; endfunction
  task automatic FUNCTION_TASK(); endtask

  // function/function
  function automatic bit function_function(); return 1'b0; endfunction
  function automatic bit FUNCTION_FUNCTION(); return 1'b0; endfunction

  // function/instance
  function automatic bit function_instance(); return 1'b0; endfunction
  sub FUNCTION_INSTANCE ();

  // instance/var
  sub instance_var ();
  logic INSTANCE_VAR;

  // instance/net
  sub instance_net ();
  wire INSTANCE_NET;

  // instance/genblock
  sub instance_genblock ();
  if (1) begin : INSTANCE_GENBLOCK
  end

  // instance/begin
  sub instance_begin ();
  initial begin : INSTANCE_BEGIN
  end

  // instance/fork
  sub instance_fork ();
  initial fork : INSTANCE_FORK
  join

  // instance/task
  sub instance_task ();
  task automatic INSTANCE_TASK(); endtask

  // instance/function
  sub instance_function ();
  function automatic bit INSTANCE_FUNCTION(); return 1'b0; endfunction

  // instance/instance
  sub instance_instance ();
  sub INSTANCE_INSTANCE ();

  // Unchecked declaration sorting first must not be reported as the original
  localparam int SORTS_FIRST = 1;
  logic [SORTS_FIRST-1:0] Sorts_First;
  logic [SORTS_FIRST-1:0] sorts_first;

endmodule

module sub;
endmodule

interface Ifc;
  logic modport_name;
  modport MODPORT_NAME (input modport_name);
endinterface

// Constraint: should not warn
class Cls;
  rand int constraint_name;
  constraint CONSTRAINT_NAME {constraint_name > 0;}
endclass

package pkg;
  localparam logic [7:0] REG_CTRL = 8'h00;
endpackage
