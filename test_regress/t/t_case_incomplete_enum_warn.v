module test_bug;
    // Define an enum with 4 states
    typedef enum logic [1:0] {
        STATE_IDLE  = 2'd0,
        STATE_READ  = 2'd1,
        STATE_WRITE = 2'd2,
        STATE_ERROR = 2'd3
    } system_state_t;

    system_state_t current_state;

    initial begin
        current_state = STATE_IDLE;
        
        // We only cover IDLE and READ.
        // We intentionally leave out WRITE and ERROR!
        unique case (current_state)
            STATE_IDLE: $display("Idling...");
            STATE_READ: $display("Reading...");
        endcase
    end
endmodule