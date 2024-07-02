module seq_detector_tb
  #( parameter seq = 7'b1010011
   )
   (
 	input clk,
 	input rst,
 	input data_tb,
 	output reg match_tb
   );
 
  reg [$clog2(7)-1:0]match_counter;
  
  initial begin
    match_counter = 3'b0;
  end

  always @ (posedge clk) begin
    if (rst) begin
      match_counter <= 0;
    end

    else begin
      if(data_tb == seq[match_counter]) begin
        match_counter <= match_counter +1;
      end
      else if (data_tb == 1) begin
        match_counter <= 1;
      end
      else if (data_tb == 0) begin
	match_counter <= 0;
      end
    end
  end

  always @ (*) begin
    if (match_counter == 6 && data_tb ==1) begin
      match_tb =1'b1;
    end
    else begin
      match_tb =1'b0;
    end
  end

  `ifdef FORMAL
  
  `ifdef VERIFIC

    match_check: cover property (@(posedge clk) disable iff (rst) (match_tb));   

 `endif //VERIFIC
 `endif //FORMAL
  
endmodule
