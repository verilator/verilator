module t;
    typedef struct {
        struct {
            logic m0;
            logic [3:0] m1;
            logic m2;
        } sub;
    } struct_t;
    struct_t s1;
    struct_t s2;

    assign {s1.sub.m0, s1.sub.m1, s1.sub.m2} = {1'b0, 4'h5, 1'b1};
    assign {s2.sub.m0, s2.sub.m1, s2.sub.m2} = {1'b0, 4'h5, 1'b1};

    initial begin
        if(s1 != s2) begin
            $fatal;
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
