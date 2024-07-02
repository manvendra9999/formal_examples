module seq_detector_case
  #( parameter seq = 7'b1010011
   )
   (
 	input clk,
 	input rst,
 	input data_case,
 	output reg match_case
   );
 
  typedef enum reg [$clog2(7)-1:0]{
  S0,
  S1,
  S2,
  S3,
  S4,
  S5,
  S6
  } state_t;

  reg [$clog2(7)-1:0] state_counter;

  initial begin
    match_case =1'b0;
    state_counter = S0;
  end

  always @ (posedge clk) begin
    if (rst) begin
      state_counter <= S0;
    end
    //#( parameter seq = 7'b1010011
    else begin
      case (state_counter)
        S0: state_counter <= (data_case == 1) ? S1:S0;
	S1: state_counter <= (data_case == 0) ? S2:S1;
	S2: state_counter <= (data_case == 1) ? S3:S0;
	S3: state_counter <= (data_case == 0) ? S4:S1;
	S4: state_counter <= (data_case == 0) ? S5:S3;
	S5: state_counter <= (data_case == 1) ? S6:S0;
	S6: state_counter <= (data_case == 1) ? S1:S2;
      endcase
    end
  end

  always @(*) begin
    if (state_counter == S6 & data_case ==1) begin
      match_case = 1'b1;
    end

    else begin
     match_case = 1'b0;
    end
  end


  `ifdef FORMAL
  
  `ifdef VERIFIC

     match_check: cover property (@(posedge clk) disable iff (rst) (match_case));
    

  `endif //VERIFIC

  `endif //FORMAL
  
endmodule
