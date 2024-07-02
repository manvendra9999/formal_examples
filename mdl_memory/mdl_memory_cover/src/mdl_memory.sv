module mdl_memory
  #(
       parameter DEPTH = 16,
       parameter WIDTH = 8
  )
  
  (
    input clk,
    input rst,
    input vld_in,
    input reg [$clog2(DEPTH)-1:0]wr_addr,
    input [WIDTH-1:0] data_in,
    input vld_out,
    input reg [$clog2(DEPTH)-1:0]rd_addr,
    output logic [WIDTH-1:0] data_out
  );
  
  logic [WIDTH-1:0] mem [DEPTH-1:0];
  
  initial begin
    for (int i=0; i <= DEPTH-1; i++) begin
      mem[i] <= {WIDTH{1'b0}};
    end
//    wr_addr <= 0;
//    rd_addr <= 0;
  end


  // data write
  always @ (posedge clk) begin
    if (rst) begin
      for (int i=0; i <= DEPTH-1; i++) begin
        mem[i] <= {WIDTH{1'b0}};
      end
    end
    else if (vld_in) begin
      mem[wr_addr] <= data_in;
    end
  end
  
  //data read
  always @ (*) begin
    data_out = 'b0;
    if (vld_out & vld_in & (wr_addr == rd_addr)) begin
      data_out = data_in;
    end
    else if (vld_out) begin
      data_out = mem[rd_addr];
    end
  end

  `ifdef FORMAL
  
  `ifdef VERIFIC
    //assume
    

    // assert

    //covers
    genvar i;
     generate 
       for (i = 0; i < DEPTH; i++) begin  
         cover_push_pointer: cover property (@(posedge clk) disable iff (rst) (wr_addr == i));
         cover_read_add:     cover property (@(posedge clk) disable iff (rst) (rd_addr == i));
       end
     endgenerate



  `endif //VERIFIC
  `endif //FORMAL
  
endmodule
