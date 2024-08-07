// ------------------ [AW] ------------------
int pass_write_addr, total_write_addr;

property write_addr_op_p;
  @(posedge clk) disable iff(!rst_n)
  (HREADY && HWRITE && (HTRANS == NONSEQ) && (~AWVALID)) |-> ##1((AWADDR == $past(HADDR, 1)) && (AWVALID));
endproperty

write_addr_check: assert property(write_addr_op_p) begin
  pass_write_addr++;     total_write_addr++;
  $display("1.  ->  [  OK  ] ADDRESS mapped at \t\t%0tns", $time/1);
end
else begin
  total_write_addr++;
  $display("1.  ->  [FAILED] ADDRESS mapped at \t\t%0tns", $time/1);
end

// -- aw_handshake
property handshake_wr_addr_p;
  @(posedge clk) disable iff(!rst_n)
  (AWVALID && AWREADY && HTRANS != IDLE) |-> ##1($fell(AWVALID));
endproperty

int pass_wr_addr_hs, total_wr_addr_hs;
handshake_write_addr: assert property (handshake_wr_addr_p) begin
  pass_wr_addr_hs++;     total_wr_addr_hs++;
  $display("3.  ->  [  OK  ] ADDRESS handshake at \t%0tns", $time/1);
end
else begin
  pass_wr_addr_hs++;
  $display("3.  ->  [FAILED] ADDRESS handshake at \t%0tns", $time/1);
end
// -------------------------------------------


// ------------------- [W] -------------------
int pass_write_data, total_write_data;

// -- single burst
property wr_data_single_busrt_op_p;
  @(posedge clk) disable iff(!rst_n)
  (HWRITE && (HBURST == SINGLE) && (HTRANS == NONSEQ) && HREADY) |-> ##2((WDATA == HWDATA) && (WVALID));
endproperty

wr_data_single_busrt_check: assert property(wr_data_single_busrt_op_p) begin
  pass_write_data++;     total_write_data++;
  $display("2.  ->  [  OK  ] DATA mapped at \t\t%0tns", $time/1);
end
else begin
  total_write_data++;
  $display("2.  ->  [FAILED] DATA mapped at \t\t%0tns", $time/1);
end

// -- multiple burst
property wr_data_multi_burst_op_p;
  @(posedge clk) disable iff(!rst_n)
  (HWRITE && (HBURST != SINGLE) && ff_rd_valid[WRITE] && (HTRANS != IDLE)) |-> ##1((WDATA == $past(HWDATA, 2)) && WVALID);
endproperty

wr_data_multi_burst_check: assert property(wr_data_multi_burst_op_p) begin
  pass_write_data++;     total_write_data++;
  $display("\n...New transfer...");
  $display("2.  ->  [  OK  ] DATA mapped at \t\t%0tns", $time/1);
end
else begin
  total_write_data++;
  $display("2.  ->  [FAILED] DATA mapped at \t\t%0tns", $time/1);
end

// -- w_handshake
property handshake_wr_data_p;
  @(posedge clk) disable iff(!rst_n)
  (HWRITE && (HBURST != SINGLE) && (HTRANS != IDLE) && ff_rd_valid[WRITE]) |-> ##1(WVALID);
endproperty

int pass_wr_data_hs, total_wr_data_hs;
handshake_write_data: assert property (handshake_wr_data_p) begin
  pass_wr_data_hs++;     total_wr_data_hs++;
  $display("3.  ->  [  OK  ] DATA handshake at \t\t%0tns", $time/1);
end
else begin
  total_wr_data_hs++;
  $display("3.  ->  [FAILED] DATA handshake at \t\t%0tns", $time/1);
end
// -------------------------------------------


// ----------------- [BREADY] ----------------
property bready_op_p;
  @(posedge clk) disable iff(!rst_n)
  (WVALID && WREADY && WLAST && (HTRANS != IDLE)) |-> ##1(BREADY);
endproperty

bready_check: assert property(bready_op_p) begin
  $display("3.  ->  [  OK  ] BREADY rose at \t\t%0tns", $time/1);
end
else begin
  $display("3.  ->  [FAILED] BREADY rose at \t\t%0tns", $time/1);
end
// -------------------------------------------


// ----------------- [BRESP] -----------------
int pass_write_resp, total_write_resp;

// -- okay
property write_resp_op_p_1;
  @(posedge clk) disable iff(!rst_n)
  ($rose(BVALID) && BRESP[1] == 1'b0) |-> ##1 (HRESP == 1'b0 && HREADY == 1'b1);
endproperty

write_resp_check_1: assert property(write_resp_op_p_1) begin
  pass_write_resp++;     total_write_resp++;
  $display("4.  ->  [  OK  ] RESP mapped at \t\t%0tns", $time/1);
end
else begin
  total_write_resp++;
  $display("4.  ->  [FAILED] RESP mapped at \t\t%0tns", $time/1);
end

// -- error
property write_resp_op_p_2;
  @(posedge clk) disable iff(!rst_n)
  ($rose(BVALID) && BRESP[1] == 1'b1) |-> ##1 (HRESP == 1'b1 && HREADY == 1'b0);
endproperty

write_resp_check_2: assert property(write_resp_op_p_2) begin
  pass_write_resp++;     total_write_resp++;
  $display("4.  ->  [  OK  ] RESP mapped at \t\t%0tns", $time/1);
end
else begin
  total_write_resp++;
  $display("4.  ->  [FAILED] RESP mapped at \t\t%0tns", $time/1);
end

// -- b_hanshake
property handshake_wr_resp_p;
  @(posedge clk) disable iff(!rst_n)
  (BREADY && BVALID) |-> ##1($fell(BREADY));
endproperty

int pass_wr_resp_hs, total_wr_resp_hs;
handshake_write_resp: assert property (handshake_wr_resp_p) begin
  pass_wr_resp_hs++;     total_wr_resp_hs++;
  $display("4.  ->  [  OK  ] RESP handshake at \t\t%0tns", $time/1);
end
else begin
  total_wr_resp_hs++;
  $display("4.  ->  [FAILED] RESP handshake at \t\t%0tns", $time/1);
end
// -------------------------------------------


// ----------------- [ERROR] -----------------
property write_err_p;
  @(posedge clk) disable iff(!rst_n)
  ((BRESP[1] == 1'b1) && BVALID && BREADY) |-> ##1(HREADY == 1'b0) |-> ##1(HREADY == 1'b1);
endproperty

write_err_check: assert property(write_err_p) begin
  $display("4.  ->  [  OK  ] ERR_RESP mapped at \t%0tns", $time/1);
end
else begin
  $display("4.  ->  [FAILED] ERR_RESP mapped at \t%0tns", $time/1);
end
// -------------------------------------------


// ----------- [New transaction] -------------
property new_transac_check_p;
  @(posedge clk) disable iff(!rst_n)
  ((HTRANS == NONSEQ) && HREADY && (HBURST != SINGLE) && HWRITE) |-> ((transfer_cnt == 0));
endproperty

new_transac_check: assert property (new_transac_check_p) else $display("    ->  [FAILED] Reset signals for new transaction...");
// -------------------------------------------


// ------------- [transfer_cnt] --------------
int pass_transfer_cnt, total_transfer_cnt;

property transfer_count_check_p;
  @(posedge clk) disable iff(!rst_n)
  (((HBURST != SINGLE) && (HTRANS == NONSEQ) && (~HREADY) && BVALID && BREADY) || ((HBURST != SINGLE) && (HTRANS == NONSEQ) && ~HWRITE &&HREADY && ff_rd_valid[READ])) |-> ((transfer_cnt == AWLEN) || (transfer_cnt == ARLEN));
endproperty

transfer_count_check: assert property (transfer_count_check_p) begin
  pass_transfer_cnt++;     total_transfer_cnt++;
end
else begin
  total_transfer_cnt++;
  $display("    ->  [FAILED] transfer_cnt got wrong...");
end
// -------------------------------------------