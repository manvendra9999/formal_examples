module fifo
  #(
       parameter DEPTH = 16,
       parameter WIDTH = 8
  )
  
  (
    input clk,
    input rst,
    input push,
    input [WIDTH-1:0] data_in,
    input pop,
    output logic [$clog2(DEPTH)-1:0] pop_pointer,
    output logic mem_full,
    output logic mem_empty,
    output logic [WIDTH-1:0] data_out
  );
  
  logic [WIDTH-1:0] mem [DEPTH-1:0];
  logic [$clog2(DEPTH)-1:0] push_pointer;
//  logic [$clog2(DEPTH)-1:0] pop_pointer;
  logic roll_pointer;
  
  initial begin
    push_pointer <= 0;
    pop_pointer <= 0;
    mem_full <= 0;
    mem_empty <= 1;
    for (int i=0; i <= DEPTH-1; i++) begin
      mem[i] <= {WIDTH{1'b0}};
    end
      roll_pointer <= 'b0;
  end


  // data write
  always @ (posedge clk) begin
    if (rst) begin
      for (int i=0; i <= DEPTH-1; i++) begin
        mem[i] <= {WIDTH{1'b0}};
      end
    end
    else if (push & !mem_full) begin
      mem[push_pointer] <= data_in;
    end
  end
  
  //push pointer
  always @ (posedge clk) begin
    if (rst) begin
      push_pointer <= 'b0;
    end
    else if (push) begin
      push_pointer <= (push_pointer + 'b1) % DEPTH;
    end
  end
  
  //data read
  always @ (*) begin
    data_out = 'b0;
    if (pop & !mem_empty) begin
      data_out = mem[pop_pointer];
    end
  end

  //pop pointer
  always @ (posedge clk) begin
    if (rst) begin
      pop_pointer <= 'b0;
    end
    else if (pop) begin
      pop_pointer <= (pop_pointer + 'b1) % DEPTH;
    end
  end

  //roll_pointer
  always @ (posedge clk) begin
    if (rst) begin
      roll_pointer <= 'b0;
    end
    else if ((push & pop) & (push_pointer == (DEPTH-1) & pop_pointer == (DEPTH-1))) begin
      roll_pointer <= roll_pointer;
    end
    else if (push & (push_pointer == (DEPTH-1))) begin
      roll_pointer <= !roll_pointer;
    end
    else if (pop & (pop_pointer == (DEPTH-1))) begin
      roll_pointer <= !roll_pointer;
    end
  end
  
  //mem empty
  assign mem_empty = !roll_pointer & (pop_pointer == push_pointer);
  
  //mem full
  assign mem_full = roll_pointer & (pop_pointer == push_pointer);
 
 


  `ifdef FORMAL
  
  `ifdef VERIFIC
    //assume
    mem_empty_pop: assume property (@(posedge clk) disable iff (rst) mem_empty & !push |-> !pop);
    mem_full_push: assume property (@(posedge clk) disable iff (rst) mem_full & !pop |-> !push);
    

    // assert
    ap_raddr3: assert property (@(posedge clk) disable iff (rst) !pop && !mem_full  |=> $stable(pop_pointer));
    ap_waddr3: assert property (@(posedge clk) disable iff (rst) !push && !mem_empty |=> $stable(push_pointer));

    //covers
    genvar i;
     generate 
       for (i = 0; i < DEPTH; i++) begin  
         ap_waddr: cover property (@(posedge clk) disable iff (rst) (push_pointer == i));
       end
     endgenerate

    push_pop_cover: cover property (@(posedge clk) disable iff (rst) (push & pop));
    mem_full_cover: cover property (@(posedge clk) disable iff (rst) (mem_full));
    mem_empty_check: cover property (@(posedge clk) disable iff (rst) (mem_full));
    roll_cover: cover property (@(posedge clk) disable iff (rst) (roll_pointer));
    push_pop_roll_cover: cover property (@(posedge clk) disable iff (rst) ((push & pop) & ((push_pointer == 0) & (pop_pointer == 0))));


 `endif //VERIFIC
 `endif //FORMAL
  
endmodule
