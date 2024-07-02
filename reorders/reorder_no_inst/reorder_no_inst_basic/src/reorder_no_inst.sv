module reorder_no_inst
# (  
     parameter PKT_NUM = 7,
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

// Initial values
  initial begin
    mem_sop_pkt_id_wr_addr <=0;
    mem_sop_pkt_id_rd_addr <=0;
    mem_sop_pkt_id_out <=0;
    mem_vld_pkt_data_out <= 0;
    state_counter <= 0;
    mem_vld_pkt <=0;
    mem_sop <=0;
    mem_mop <=0;
    mem_eop <=0;
  end



// SAVING AND READING SOP PKT_IDS  
  reg [$clog2(PKT_NUM)-1:0] mem_sop_pkt_id [PKT_NUM-1:0];
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
	    mem_sop_pkt_id_rd_addr <= mem_sop_pkt_id_rd_addr + 'b1;
    end
  end

//   always @ (posedge clk) begin
//     if (rst) begin
//       for (int i=0; i <= PKT_NUM-1; i++) begin
//         mem_sop_pkt_id[i] <= 'b0;
//       end
//     end
//     else if (vld_in & SOP_in) begin
//       mem_sop_pkt_id[mem_sop_pkt_id_wr_addr] <= pkt_id_in;
//     end
//   end

//   always @ (posedge clk) begin
//   mem_sop_pkt_id_out = mem_sop_pkt_id[mem_sop_pkt_id_rd_addr];
//  end

 
   localparam DATA_SZ = $clog2(PKT_NUM);
   
 
  mdl_memory #(PKT_NUM, DATA_SZ) inst_mem_sop_pkt_id
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
      mem_vld_pkt[pkt_id_in] <= 'b1;
      mem_vld_pkt[mem_sop_pkt_id_out] <= 'b0;
    end
    else if (vld_in & EOP_in) begin
      mem_vld_pkt[pkt_id_in] <= 'b1;
    end
    else if (state_counter == S2) begin
      mem_vld_pkt[mem_sop_pkt_id_out] <= 'b0;
    end
  end
  
  always @ (posedge clk) begin
    mem_vld_pkt_data_out <= mem_vld_pkt[mem_sop_pkt_id_out];  
  end
  
// SAVING SOP DATA_IN  
  reg [PKT_NUM-1:0] mem_sop;
  
  always @ (posedge clk) begin
    if (vld_in & SOP_in) begin
      mem_sop[pkt_id_in] = data_in;
    end
  end


// SAVING MOP DATA_IN  
  reg [PKT_NUM-1:0] mem_mop;
  
  always @ (posedge clk) begin
    if (vld_in & (!SOP_in & !EOP_in)) begin
      mem_mop[pkt_id_in] = data_in;
    end
  end

// SAVING EOP DATA_IN  
  reg [PKT_NUM-1:0] mem_eop;
  
  always @ (posedge clk) begin
    if (vld_in &  EOP_in) begin
      mem_eop[pkt_id_in] = data_in;
    end
  end


// Output of all the data through state machine
  typedef enum reg [1:0]
  {S0,S1,S2} state_t;
  reg [1:0] state_counter;

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
      data_out = mem_sop[mem_sop_pkt_id_out];
    end
    else if (state_counter == S1) begin
      data_out = mem_mop[mem_sop_pkt_id_out];
    end
    else if (state_counter == S2) begin
      data_out = mem_eop[mem_sop_pkt_id_out];
    end
  end
  
  always @ (*) begin
    if (mem_vld_pkt_data_out == 1 & state_counter == S0) begin
      vld_out = 'b1;
      SOP_out = 'b1;
    end
    else if (state_counter == S1) begin
      vld_out = 'b1;
      SOP_out = 'b0;
      EOP_out = 'b0;
    end
    else if (state_counter == S2) begin
      vld_out = 'b1;
      EOP_out = 'b1;
    end
    else
      vld_out = 'b0;
  end


  `ifdef FORMAL
  `ifdef VERIFIC

//     genvar i;
//      generate 
//        for (i = 0; i < PKT_NUM; i++) begin  
//          cover_push_pointer: cover property (@(posedge clk) disable iff (rst) (mem_sop_pkt_id_wr_addr == i));
//          cover_read_add:     cover property (@(posedge clk) disable iff (rst) (mem_sop_pkt_id_rd_addr == i));
//        end
//      endgenerate
  //assuem
  //vld_in_high: assume property (@(posedge clk) disable iff (rst) (vld_in & SOP_in));

  `endif //VERIFIC
  `endif //FORMAL
endmodule
