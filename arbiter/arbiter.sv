module arbiter
  #(
 	parameter NUM_REQ = 16
   ) (
 	input clk,
 	input rst,
 	input [NUM_REQ-1:0] req,
 	output reg [NUM_REQ-1:0]grant
   );
 
  reg [$clog2(NUM_REQ)-1:0] grant_pointer;
  reg [$clog2(NUM_REQ)-1:0] grant_pointer_last;

  initial begin
	grant_pointer <= 0;
	grant_pointer_last <=0;
	for (int i=0; i <= NUM_REQ-1; i++) begin
  	grant[i] <= 1'b0;
	end
  end

  always @ (*) begin
  	grant_pointer = grant_pointer_last;
    	for (int i=0; i <= NUM_REQ-1; i++) begin
      	   if (req[((i + 1 + grant_pointer_last) % NUM_REQ)] == 1 &&
                  (grant_pointer == grant_pointer_last)) begin
   	          grant_pointer = (i + 1 + grant_pointer_last) % NUM_REQ;
      	   end
        	end	 
  end

  always @ (posedge clk) begin
	if (rst) begin
       	     grant_pointer_last <= 'b0;
	end
	else begin
    	     grant_pointer_last <= grant_pointer;
	end   	 
  end
 
  always @ (*) begin
    for (int i =0; i<= NUM_REQ-1; i++)begin
      grant[i]= 'b0;
    end
    if (|req) begin
      grant[grant_pointer] = 'b1;
    end
  end



  `ifdef FORMAL
  
  `ifdef VERIFIC
//    // if we have verific we can also do the following additional tests
//    // read/write enables enable
//
  onehot_grant: assert property (@(posedge clk) disable iff (rst) |req |-> $onehot(grant));
//    ap_waddr2: assert property (@(posedge clk) disable iff (rst) push |=> $changed(push_pointer));
//
//    // read/write needs enable UNLESS full/empty
//    ap_raddr3: assert property (@(posedge clk) disable iff (rst) !pop && !mem_full  |=> $stable(pop_pointer));
//    ap_waddr3: assert property (@(posedge clk) disable iff (rst) !push && !mem_empty |=> $stable(push_pointer));
//    ap_waddr4: assert property (@(posedge clk) disable iff (rst) (push_pointer == pop_pointer) |-> (mem_full|| mem_empty));
//
//    //ap_waddr5: cover property (@(posedge clk) disable iff (rst) (push_pointer == DEPTH-1));
    genvar i;
     generate 
       for (i = 0; i < NUM_REQ ; i++) begin  
         grant_bit_wise: cover property (@(posedge clk) disable iff (rst) (grant[i]));
       end
    endgenerate
//
//    push_pop_check: cover property (@(posedge clk) disable iff (rst) (push & pop));
//    mem_full_check: cover property (@(posedge clk) disable iff (rst) (mem_full));
//
//
    

 `endif //VERIFIC
//    data_in_1: assume property (@(posedge clk) disable iff (rst) (data_in=='d1));
  `endif //FORMAL
  
endmodule
