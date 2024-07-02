module seq_detector_mem
  #( parameter seq = 7'b0000000
   )
   (
 	input clk,
 	input rst,
 	input data_mem,
 	output reg match_mem
   );
 
  reg [6:0] mem;
  reg [6:0] mem_live;

  reg [5:0] rst_d;

  initial begin
    for (int i=0; i <= 6; i++) begin
      mem[i] = 1'b0;
      rst_d[i] = 1'b0;
    end
  end

  always @ (posedge clk) begin
    if (rst) begin
      rst_d <= 'b0;
    end
    else begin
    rst_d[0] <= 1'b1;
    rst_d[5:1] <= rst_d[4:0];
    end
  end

  always @ (posedge clk) begin
    if (rst) begin
      for (int i=0; i<=6; i++) begin
        mem[i] <=1'b0;
      end
    end
    else begin
      mem[0] <= data_mem;
      for (int i=1; i<=6; i ++ ) begin
        mem[i] <= mem[i-1];
      end
    end
  end

  always @(*) begin
    mem_live[0]=data_mem;
    for (int i=1; i<=6; i++) begin
      mem_live[i] = mem [i-1];
    end
  end
 
  always @ (*) begin
    if ((mem_live == seq) & (&rst_d)) begin
      match_mem = 1'b1;
    end
    else
      match_mem = 1'b0;
  end


  `ifdef FORMAL
  
  `ifdef VERIFIC
    match_check: cover property (@(posedge clk) disable iff (rst) (match_mem));
 
  `endif
  `endif //FORMAL
  
endmodule
