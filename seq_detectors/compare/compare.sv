module compare
  #( parameter seq = 7'b1010011
   )
   (
 	input clk,
 	input rst,
 	input data_compare
   );

  wire match_1;
  wire match_2;

  seq_detector_mem #(seq) inst_seq_detector_mem (
    .clk        (clk),
    .rst        (rst),
    .data_mem   (data_compare),
    .match_mem  (match_1)
  );

  // Instantiating ModuleB from its own file
  seq_detector_case #(seq) inst_seq_detector_case (
    .clk        (clk),  // Connect ModuleB's input to ModuleA's output
    .rst        (rst),
    .data_case  (data_compare),
    .match_case (match_2)
  );



  `ifdef FORMAL
  
  `ifdef VERIFIC
    match_cover: cover property (@(posedge clk) disable iff (rst) (match_1 & match_2));
    match_assert: assert property (@(posedge clk) disable iff (rst) (match_1 == match_2));
  `endif
  `endif //FORMAL
  
endmodule
