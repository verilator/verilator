module t
  (/*AUTOARG*/
   // Inputs
   clk
   );

  input clk;

  int   cyc = 0;


  // Test for https://github.com/verilator/verilator/issues/3364
  // Make sure all SV queue API is supported and verilator can generate
  // compile-able C++ models for it.

  // simple queue
  logic [31:0] my_int_queue [$];

  // On the functions and tasks, the my_int_queue.pop_[front|back]() call will
  // have nodep->firstAbovep() != nullptr. Because the pop_front or pop_back is
  // the first node on the "list".
  // To fix this, V3Width.cpp will not use firstAbovep(), and instead us
  // isStandalongStmt() -- which checks if the pop_front or pop_back is
  // 2nd or later, or if it's first in the list that it's in a "block" of code.
  // For functions/tasks, that is checked with:
  // VN_IS(backp(), NodeFTask)=True, so even though
  function automatic void f_pop_back__my_int_queue();
    void'(my_int_queue.pop_back());
  endfunction : f_pop_back__my_int_queue

  function automatic void f_pop_front__my_int_queue();
    void'(my_int_queue.pop_front());
  endfunction : f_pop_front__my_int_queue

  task automatic t_pop_back__my_int_queue();
    void'(my_int_queue.pop_back());
  endtask : t_pop_back__my_int_queue

  task automatic t_pop_front__my_int_queue();
    void'(my_int_queue.pop_front());
  endtask : t_pop_front__my_int_queue


  task automatic do_random_queue_operation();
    bit [7:0] rand_op;
    int       rand_index;
    logic [31:0] item;


    rand_op = 8'($urandom_range(32, 0));
    case(rand_op)
    8'd0: ; // nop

    // pushes (2x of these)
    8'd1, 8'd2: my_int_queue.push_back($urandom);
    8'd3, 8'd4: my_int_queue.push_front($urandom);

    // delete:
    8'd5: my_int_queue.delete();

    // insert(index, item):
    8'd6: begin
      rand_index = $urandom_range(my_int_queue.size());
      my_int_queue.insert(rand_index, item);
    end

    // shuffle
    8'd7: my_int_queue.shuffle();

    // Various pops for rand_op >= 8:
    // pops to var
    // V3Width debug -- firstAbovep()=ASSIGN (which I guess does the ; for us
    //                                        so we don't need the queue op to
    //                                        do it.)
    // isStandalongStmt() will ignore ASSIGN, return false (NodeAssign is
    // child of AstNodeStmt)
    8'd8: if (my_int_queue.size() > 0) item = my_int_queue.pop_front();
    8'd9: if (my_int_queue.size() > 0) item = my_int_queue.pop_back();

    // pops to the void
    // V3Width debug -- firstAbovep()=IF
    // This is fixed with isStandalongStmt() -- VN_IS(backp(), NodeIf)=True
    8'd10: if (my_int_queue.size() > 0) void'(my_int_queue.pop_front());
    8'd11: if (my_int_queue.size() > 0) void'(my_int_queue.pop_back());

    // pop result to the lhs of a condition, and do something with it.
    8'd12:
      if (my_int_queue.size() > 0)
        // V3Width debug -- firstAbovep()=LTE (good we don't want a ; here)
        if (my_int_queue.pop_front() <= 2022)
          my_int_queue.push_front(3022); // living in the year 3022.

    // pop result to the rhs of a condition, and do something with it.
    8'd13:
      if (my_int_queue.size() > 0)
        // V3Width debug -- firstAbovep()=GT (good we don't want a ; here)
        if (4022 > my_int_queue.pop_front())
          my_int_queue.push_front(3023); // living in the year 3023.

    // pops to the void after yet another case:
    // V3Width debug -- firstAbovep()=CASEITEM (not a nullptr)
    // This is fixed with isStandalongStmt() -- VN_IS(backp(), CaseItem)=True
    8'd14:
      case (my_int_queue.size() > 0)
      0: ;
      1: void'(my_int_queue.pop_front());
      default: ;
      endcase // case (my_int_queue.size() > 0)

    // V3Width debug -- firstAbovep()=CASEITEM (not a nullptr)
    // backp()->nextp()=CASEITEM (different one)
    // This is fixed with isStandalongStmt() -- VN_IS(backp(), CaseItem)=True
    8'd15:
      case (my_int_queue.size() > 0)
      0: ;
      1: void'(my_int_queue.pop_back());
      default;
      endcase // case (my_int_queue.size() > 0)

    // pops in a function or task
    8'd16: if (my_int_queue.size() > 0) f_pop_back__my_int_queue();
    8'd17: if (my_int_queue.size() > 0) f_pop_front__my_int_queue();
    8'd18: if (my_int_queue.size() > 0) t_pop_back__my_int_queue();
    8'd19: if (my_int_queue.size() > 0) t_pop_front__my_int_queue();

    // But what if we put some dummy code before the pop_back() or pop_front():
    8'd20: begin
      if (my_int_queue.size() > 0) begin
        ; // dummy line
        // V3Width debug -- firstAbovep()=BEGIN (is not nullptr).
        // This is fixed with isStandalongStmt() -- VN_IS(backp(), NodeIf)=True
        void'(my_int_queue.pop_back());
      end
    end
    8'd21: begin
      automatic int temp_int = 0;
      if (my_int_queue.size() > 0) begin
        temp_int = 5; // dummy line
        // V3Width debug -- firstAbovep()=nullptr (good)
        void'(my_int_queue.pop_back());
      end
    end
    8'd22: begin
      if (my_int_queue.size() > 0) begin
        automatic int some_temp_dummy_int;
        some_temp_dummy_int = 42;
        // V3Width debug -- firstAbovep()=nullptr (good)
        void'(my_int_queue.pop_back());
      end
    end
    8'd23: begin
      if (my_int_queue.size() > 0) begin
        // no dummy here, just a 'begin' helper before it.
        // V3Width debug -- firstAbovep()=BEGIN (is not nullptr).
        // This is fixed with isStandalongStmt() -- VN_IS(backp(), NodeIf)=True
        void'(my_int_queue.pop_back());
      end
    end

    // What about an if of something else, followed by a pop_front?
    8'd24: begin
      automatic int temp_int = 0;
      if (my_int_queue.size() == 0) begin // dummy
        temp_int = 1000;
      end
      void'(my_int_queue.pop_front()); // firstAbovep() should be nullptr here.
    end


    default: ; // nop
    endcase // case (rand_op)

  endtask : do_random_queue_operation



  always @ (posedge clk) begin : main
    cyc <= cyc + 1;

    do_random_queue_operation();

    if (cyc > 100) begin
      $write("*-* All Finished *-*\n");
      $finish();
    end
  end



endmodule : t
