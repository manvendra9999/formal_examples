
module puzzle853(
   input clk,
   input rst
);


reg [3:0] bkt8;
reg [3:0] bkt5;
reg [3:0] bkt3;
reg [31:0] cycle_counter;
reg rst_1d;
reg bkt8_2_bkt5;
reg bkt5_2_bkt8;
reg bkt8_2_bkt3;
reg bkt3_2_bkt8;
reg bkt5_2_bkt3;
reg bkt3_2_bkt5;
wire [5:0] transition;
assign transition = {bkt3_2_bkt5, bkt5_2_bkt3, bkt3_2_bkt8, bkt8_2_bkt3, bkt5_2_bkt8, bkt8_2_bkt5};


initial begin
  cycle_counter <= 32'd0;
  rst_1d <= 1'b1;
end

always @(posedge clk) begin
  rst_1d <= rst;
end


always @(posedge clk) begin
        if (rst) begin
            cycle_counter <= 32'b0;
        end else begin
            cycle_counter <= cycle_counter + 32'b1;
        end
    end

`ifdef FORMAL
`ifdef VERIFIC

//initial value of bkt8=8, bkt5=0, bkt3=0
init_bkt_val: assume property (@ (posedge clk) disable iff (rst)
  rst_1d |-> ((bkt8 == 4'd8) && (bkt5 == 4'd0) && (bkt3 == 4'd0) && !(|transition))
  );



// Sum is 8
sum8: assume property (@ (posedge clk)  disable iff (rst)
  (bkt8 + bkt5 + bkt3) == 4'd8);

//values for bucktes are constrained
value_bkt8: assume property (@ (posedge clk)  disable iff (rst)
  (bkt8 >=4'd0) && (bkt8 <= 4'd8));

value_bkt5: assume property (@ (posedge clk)  disable iff (rst)
  (bkt5 >=4'd0) && (bkt5 <= 4'd5));

value_bkt3: assume property (@ (posedge clk)  disable iff (rst)
  (bkt3 >=4'd0) && (bkt3 <= 4'd3));

// if no movement then no change
stable_bkt: assume property (@ (posedge clk)  disable iff (rst)
  !(|transition) |-> ($stable(bkt8) && $stable(bkt5) &&  $stable(bkt3))
  );


//shifting from bkt8 to bkt5
bkt8tobkt5: assume property (@ (posedge clk)  disable iff (rst)
  bkt8_2_bkt5 |-> (
    (bkt5 == ($past(bkt5) + ((5-$past(bkt5)) < $past(bkt8) ? (5-$past(bkt5)) : $past(bkt8)))) &&
    (bkt8 == ($past(bkt8) - ((5-$past(bkt5)) < $past(bkt8) ? (5-$past(bkt5)) : $past(bkt8))))
                        )
                        );
//from bkt5 to bkt8
bkt5tobkt8: assume property (@ (posedge clk)  disable iff (rst)
  bkt5_2_bkt8 |-> (
    (bkt8 == ($past(bkt8) + ((8-$past(bkt8)) < $past(bkt5) ? (8-$past(bkt8)) : $past(bkt5)))) &&
    (bkt5 == ($past(bkt5) - ((8-$past(bkt8)) < $past(bkt5) ? (8-$past(bkt8)) : $past(bkt5))))
                        )
                        );

//from bkt8 to bkt3
bkt8tobkt3: assume property (@ (posedge clk)  disable iff (rst)
  bkt8_2_bkt3 |-> (
    (bkt3 == ($past(bkt3) + ((3-$past(bkt3)) < $past(bkt8) ? (3-$past(bkt3)) : $past(bkt8)))) &&
    (bkt8 == ($past(bkt8) - ((3-$past(bkt3)) < $past(bkt8) ? (3-$past(bkt3)) : $past(bkt8))))
                        )
                        );
//from bkt3 to bkt8
bkt3tobkt8: assume property (@ (posedge clk)  disable iff (rst)
  bkt3_2_bkt8 |-> (
    (bkt8 == ($past(bkt8) + ((8-$past(bkt8)) < $past(bkt3) ? (8-$past(bkt8)) : $past(bkt3)))) &&
    (bkt3 == ($past(bkt3) - ((8-$past(bkt8)) < $past(bkt3) ? (8-$past(bkt8)) : $past(bkt3))))
                        )
                        );

//from bkt5 to bkt3
bkt5tobkt3: assume property (@ (posedge clk)  disable iff (rst)
  bkt5_2_bkt3 |-> (
    (bkt3 == ($past(bkt3) + ((3-$past(bkt3)) < $past(bkt5) ? (3-$past(bkt3)) : $past(bkt5)))) &&
    (bkt5 == ($past(bkt5) - ((3-$past(bkt3)) < $past(bkt5) ? (3-$past(bkt3)) : $past(bkt5))))
                        )
                        );
//from bkt3 to bkt5
bkt3tobkt5: assume property (@ (posedge clk)  disable iff (rst)
  bkt3_2_bkt5 |-> (
    (bkt5 == ($past(bkt5) + ((5-$past(bkt5)) < $past(bkt3) ? (5-$past(bkt5)) : $past(bkt3)))) &&
    (bkt3 == ($past(bkt3) - ((5-$past(bkt5)) < $past(bkt3) ? (5-$past(bkt5)) : $past(bkt3))))
                        )
                        );

// one hot for transition
one_hot: assume property (@ (posedge clk) disable iff (rst)
  $onehot0({transition})
  );

//solution cover
sol_cvr: cover property (@(posedge clk)  disable iff (rst)
  (bkt5 == 4'd4) || (bkt8 == 4'd4)
  );

//redundant cover
trv_cvr: cover property (@(posedge clk)  disable iff (rst)
 (cycle_counter == 15) |-> ($onehot(transition))
  );

trv_cvr_bkt8: cover property (@(posedge clk)  disable iff (rst)
 (cycle_counter == 3) |-> (bkt8 + bkt3 == 4'd8)
  );


`endif //VERIFIC
`endif //FORMAL
  
endmodule
