module fifo
  #(
       parameter DEPTH = 19,
       parameter WIDTH = 8
  )
  
  (
    input clk,
    input rst,
    input push,
    input [WIDTH-1:0] data_in,
    input pop,
    output logic mem_full,
    output logic mem_empty,
    output logic [WIDTH-1:0] data_out
  );
  
  logic [WIDTH-1:0] mem [DEPTH-1:0];
  //reg push_1d;
  //reg rst_1d;
  logic [$clog2(DEPTH)-1:0] push_pointer;
  //reg [$clog2(DEPTH)-1:0] push_pointer_1d;
  logic [$clog2(DEPTH)-1:0] pop_pointer;
  
  initial begin
	  push_pointer <= 0;
	  pop_pointer <= 0;
	  mem_full <= 0;
	  mem_empty <= 1;
          for (int i=0; i <= DEPTH-1; i++) begin
            mem[i] <= {WIDTH{1'b0}};
          end
  end

  // data write
  always @ (posedge clk) begin
    if (rst) begin
      for (int i=0; i <= DEPTH-1; i++) begin
        mem[i] <= {WIDTH{1'b0}};
      end
    end
    else if (push) begin
      mem[push_pointer] <= data_in;
    end
  end
  
  //push pointer
  always @ (posedge clk) begin
    if (rst) begin
      push_pointer <= 'b0;
      //push_pointer <= 4'b0;
    end
    else if (push) begin
      push_pointer <= (push_pointer + 'b1) % DEPTH;
    end
  end
  
  /*
  // 1 cycle delayed push and push pointer
  always @ (posedge clk) begin
    if (rst) begin
      push_1d        <= 'b0;
      push_pointer_1d <= 'b0;
    end
    else begin
      push_1d <= push;
      push_pointer_1d <= push_pointer;
    end
  end
  
  always @ (posedge clk) begin
    rst_1d <= rst;
    end
   */ 
  
  //pop pointer
  always @ (posedge clk) begin
    if (rst) begin
      pop_pointer <= 'b0;
    end
    else if (pop) begin
      pop_pointer <= (pop_pointer + 'b1) % DEPTH;
    end
  end
  
  //data read
  always @ (*) begin
    data_out = 'b0;
    if (pop) begin
      data_out = mem[pop_pointer];
    end
  end
  
 
  logic [$clog2(DEPTH)-1:0]push_pointer_m1;
  assign push_pointer_m1 = push_pointer-'d1;
 
 
 
  //mem empty
  always @ (posedge clk) begin
    if (rst) begin
   	  mem_empty <= 1'b1;
    end
    else if (push & !pop) begin
      mem_empty <='b0;
    end
    else if (pop & (pop_pointer == (push_pointer_m1))) begin
      mem_empty <= 1'b1;
    end
    else if ((mem_empty == 1) & (pop_pointer == push_pointer)) begin
      mem_empty <= 1'b1;
    end
   // else begin
   //   mem_empty <= 1'b0;
   // end
  end
 
  logic [$clog2(DEPTH)-1:0]pop_pointer_m1;
  assign pop_pointer_m1 = pop_pointer-'d1;


  //mem full
  always @ (posedge clk) begin
    
    if (rst) begin
   	  mem_full <= 1'b0;
    end
    else if (pop & !push) begin
      mem_full <='b0;
    end
    else if (push & (push_pointer == (pop_pointer_m1))) begin
      mem_full <= 1'b1;
    end
    else if (mem_full == 1 & (pop_pointer == push_pointer)) begin
      mem_full <= 1'b1;
    end
    //else begin
    //  mem_full <= 1'b0;
    //end
  end
  
  // preperty
  
  `ifdef FORMAL
  
`ifdef VERIFIC
    // if we have verific we can also do the following additional tests
    // read/write enables enable
    ap_raddr2: assert property (@(posedge clk) disable iff (rst) pop |=> $changed(pop_pointer));
    ap_waddr2: assert property (@(posedge clk) disable iff (rst) push |=> $changed(push_pointer));

    // read/write needs enable UNLESS full/empty
    ap_raddr3: assert property (@(posedge clk) disable iff (rst) !pop && !mem_full  |=> $stable(pop_pointer));
    ap_waddr3: assert property (@(posedge clk) disable iff (rst) !push && !mem_empty |=> $stable(push_pointer));
    ap_waddr4: assert property (@(posedge clk) disable iff (rst) (push_pointer == pop_pointer) |-> (mem_full|| mem_empty));

    //ap_waddr5: cover property (@(posedge clk) disable iff (rst) (push_pointer == DEPTH-1));
    genvar i;
     generate 
       for (i = 0; i < DEPTH; i++) begin  
         ap_waddr: cover property (@(posedge clk) disable iff (rst) (push_pointer == i));
       end
endgenerate

    push_pop_check: cover property (@(posedge clk) disable iff (rst) (push & pop));
    mem_full_check: cover property (@(posedge clk) disable iff (rst) (mem_full));



 `endif //VERIFIC
//    data_in_1: assume property (@(posedge clk) disable iff (rst) (data_in=='d1));
  `endif //FORMAL
  
endmodule
