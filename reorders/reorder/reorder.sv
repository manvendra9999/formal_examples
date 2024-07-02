module reorder
# (  
     parameter PKT_NUM = 16,
     parameter PKT_SIZE = 3,
     parameter DATA_WIDTH =1
  )
 
  (  
     input                            clk,
     input                            rst,
     input 			      vld_in,
     input  [$clog2(PKT_NUM)-1:0]     pkt_id_in,
     input  [DATA_WIDTH-1:0]          data_in,
     input                            SOP_in,
     input                            EOP_in,
     output reg                       vld_out,
     output reg[DATA_WIDTH-1:0]       data_out,
     output reg                       SOP_out,
     output reg                       EOP_out,
     output reg [$clog2(PKT_NUM)-1:0] pkt_id_out

  );



// SAVING AND READING SOP PKT_IDS  
  reg [$clog2(PKT_NUM)-1:0] mem_sop_pkt_id_wr_addr;
  reg [$clog2(PKT_NUM)-1:0] mem_sop_pkt_id_rd_addr;
  reg [$clog2(PKT_NUM)-1:0] mem_sop_pkt_id_out;
  
  always @ (posedge clk)begin
    if(rst) begin
      mem_sop_pkt_id_wr_addr <= 'b0;
    end
    else if (vld_in & SOP_in) begin
      mem_sop_pkt_id_wr_addr <= mem_sop_pkt_id_wr_addr + 'b1;
    end
  end
  
  always @ (posedge clk) begin
    if (state_counter == S2) begin
	mem_sop_pkt_id_rd_addr <= mem_sop_pkt_id_rd_addr +'b1;
    end
  end

  mdl_memory #(PKT_NUM, $clog2(PKT_NUM)) inst_mem_sop_pkt_id
  (
    .clk        (clk),
    .rst        (rst),
    .vld_in     (SOP_in & vld_in),
    .wr_addr    (mem_sop_pkt_id_wr_addr),
    .data_in    (pkt_id_in),
    .vld_out    ('b1),
    .rd_addr    (mem_sop_pkt_id_rd_addr),
    .data_out   (mem_sop_pkt_id_out)
  );

// TRAKING DATA_PKT COMPLETION (DEPENDS ON EOP_IN)  

  reg [PKT_NUM-1:0] mem_vld_pkt;
  reg mem_vld_pkt_data_out;
  
  always @ (posedge clk) begin
    if ((vld_in & EOP_in) & state_counter ==S2) begin
      mem_vld_pkt[pkt_id_in] = 'b1;
      mem_vld_pkt[mem_sop_pkt_id_out] = 'b0;
    end
    if (vld_in & EOP_in) begin
	mem_vld_pkt[pkt_id_in] = 'b1;
    end
    if (state_counter == S2) begin
	mem_vld_pkt[mem_sop_pkt_id_out] = 'b0;
    end
  end
  
  assign mem_vld_pkt_data_out = mem_vld_pkt[mem_sop_pkt_id_out];  
  
//   always @ (posedge clk) begin
//     if (state_counter == S2) begin
// 	mem_vld_pkt[mem_sop_pkt_id_out] = 'b0;
//     end
//   end
  
// SAVING SOP DATA_IN  

//  reg [$clog2(PKT_NUM)-1:0] mem_sop_rd_addr;
  reg mem_sop_data_out;
  
//   always @ (*) begin
//     if (mem_vld_pkt_data_out == 1 & state_counter == S0) begin
//       mem_sop_rd_addr = mem_sop_pkt_id_out;
//     end
//   end
//   always @ (*) begin
//     if (mem_vld_pkt_data_out == 1 & state_counter == S0) begin
//       pkt_id_out = mem_sop_pkt_id_out;
//       data_out = mem_sop_data_out;
//       vld_out = 'b1;
//     end
//   end
  
  mdl_memory #(PKT_NUM, 1) inst_mem_sop
  (
    .clk        (clk),
    .rst        (rst),
    .vld_in     (SOP_in & vld_in),
    .wr_addr    (pkt_id_in),
    .data_in    (data_in),
    .vld_out    ('b1),
    .rd_addr    (mem_sop_pkd_id_out),
    .data_out   (mem_sop_data_out)
  );


// SAVING MOP DATA_IN  
//  reg [$clog2(PKT_NUM)-1:0] mem_mop_rd_addr;
  reg mem_mop_data_out;
  
//   always @ (*) begin
//     if (state_counter == S1) begin
//       mem_mop_rd_addr = mem_sop_pkt_id_out;
//     end
//   end
  
//   always @ (*) begin
//     if (state_counter == S1) begin
//       pkt_id_out = mem_sop_pkt_id_out;
//       data_out = mem_mop_data_out;
//       vld_out = 'b1;
//     end
//   end

  mdl_memory #(PKT_NUM, 1) inst_mem_mop
  (
    .clk        (clk),
    .rst        (rst),
    .vld_in     ((!SOP_in & !EOP_in) & vld_in),
    .wr_addr    (pkt_id_in),
    .data_in    (data_in),
    .vld_out    ('b1),
    .rd_addr    (mem_sop_pkt_id_out),
    .data_out   (mem_mop_data_out)
  );


// SAVING EOP DATA_IN  
//  reg [$clog2(PKT_NUM)-1:0] mem_eop_rd_addr;
  reg mem_eop_data_out;
  
//   always @ (*) begin
//     if (state_counter == S2) begin
// 	mem_eop_rd_addr = mem_sop_pkt_id_out;
//     end
//   end

//   always @ (*) begin
//     if (state_counter == S2) begin
//         pkt_id_out = mem_sop_pkt_id_out;
// 	data_out = mem_eop_data_out;
// 	vld_out = 'b1;
//     end
//   end

  mdl_memory #(PKT_NUM, 1) inst_mem_eop
  (
    .clk        (clk),
    .rst        (rst),
    .vld_in     (EOP_in & vld_in),
    .wr_addr    (pkt_id_in),
    .data_in    (data_in),
    .vld_out    ('b1),
    .rd_addr    (mem_sop_pkt_id_out),
    .data_out   (mem_eop_data_out)
  );

// Output of all the data through state machine
  typedef enum reg [2:0]
  {S0,S1,S2} state_t;
  reg [2:0] state_counter;

  always @ (posedge clk) begin
    case (state_counter)
      S0: begin
        if (mem_vld_pkt_data_out == 1) begin
	  state_counter <= S1;
	end
	else
	  state_counter <= S0;
      end
      S1: begin
        state_counter <= S2;
      end
      S2: begin
	state_counter <= S0;
      end
    endcase
  end

  assign pkt_id_out = mem_sop_pkt_id_out;

  always @ (*) begin
    if (mem_vld_pkt_data_out == 1 & state_counter == S0) begin
      data_out = mem_sop_data_out;
    end
    else if (state_counter == S1) begin
      data_out = mem_mop_data_out;
    end
    else if (state_counter == S2) begin
      data_out = mem_eop_data_out;
    end
  end
  
  always @ (*) begin
    if (mem_vld_pkt_data_out == 1 & state_counter == S0) begin
      vld_out = 'b1;
      SOP_out = 'b1;
    end
    else if (state_counter == S1) begin
      vld_out = 'b1;
    end
    else if (state_counter == S2) begin
      vld_out = 'b1;
      EOP_out = 'b1;
    end
    else
      vld_out ='b0;
  end

endmodule
