// ------------------- [AR] ------------------
int pass_read_addr, total_read_addr;

property read_addr_op_p;
  @(posedge clk) disable iff(!rst_n)
  (~HWRITE && HREADY && (HBURST == SINGLE) && (HTRANS == NONSEQ)) || ((HBURST == INCR4) && (HTRANS == NONSEQ) && ~HWRITE) |-> ##1((ARADDR == $past(HADDR, 1)) && ARVALID);
endproperty

read_addr_check: assert property(read_addr_op_p) begin
  pass_read_addr++;     total_read_addr++;
  $display("1.  ->  [  OK  ] ADDRESS mapped at \t\t%0tns", $time/100);
end
else begin
  total_read_addr++;
  $display("1.  ->  [FAILED] ADDRESS mapped");
end

// -- ar_handshake
property handshake_rd_addr_p;
  @(posedge clk) disable iff(!rst_n)
  (ARVALID && ARREADY) |-> ##1($fell(ARVALID));
endproperty

int pass_rd_addr_hs, total_rd_addr_hs;
handshake_read_addr: assert property (handshake_rd_addr_p) begin
  pass_rd_addr_hs++;     total_rd_addr_hs++;
  $display("1.  ->  [  OK  ] ADDRESS handshake at \t%0tns", $time/100);
end
else begin
  total_rd_addr_hs++;
  $display("1.  ->  [FAILED] ADDRESS handshake");
end
// -------------------------------------------


// ----------------- [RREADY] ----------------
property rready_op_p;
  @(posedge clk) disable iff(!rst_n)
  (ARVALID && ARREADY) |-> ##1(RREADY);
endproperty

rready_check: assert property(rready_op_p) begin
  $display("2.  ->  [  OK  ] RREADY rose at \t\t%0tns", $time/100);
end
else begin
  $display("2.  ->  [FAILED] RREADY rose");
end
// -------------------------------------------


// ----------------- [RDATA] -----------------
int pass_read_data, total_read_data;

property read_data_op_p;
  @(posedge clk) disable iff(!rst_n)
  ((~HWRITE) && (HBURST == SINGLE) && RVALID && RREADY && RLAST) |-> ##1(HRDATA == RDATA);
endproperty

read_data_check: assert property(read_data_op_p) begin
  pass_read_data++;     total_read_data++;
  $display("3.  ->  [  OK  ] DATA mapped at \t\t%0tns", $time/100);
  // $display("\n...New transfer...");
end
else begin
  total_read_data++;
  $display("3.  ->  [FAILED] DATA mapped");
end

property read_data_burst_op_p;
  @(posedge clk) disable iff(!rst_n)
  (ff_rd_valid[READ] && (~HWRITE) && (HBURST != SINGLE) && (HTRANS != IDLE)) |-> ##1(HRDATA == $past(RDATA, 2));
endproperty

read_data_check_2: assert property(read_data_burst_op_p) begin
  pass_read_data++;     total_read_data++;
  $display("3.  ->  [  OK  ] DATA mapped at \t\t%0tns", $time/100);
  // $display("\n...New transfer...");
end
else begin
  total_read_data++;
  $display("3.  ->  [FAILED] DATA mapped");
end

// -- r_handshake
property handshake_rd_resp_p;
  @(posedge clk) disable iff(!rst_n)
  ((~HWRITE) && (HBURST == SINGLE) && RLAST && RVALID && RREADY) |-> ##1((~RVALID));
endproperty

int pass_rd_data_hs, total_rd_data_hs;
handshake_read_data: assert property (handshake_rd_resp_p) begin
  pass_rd_data_hs++;     total_rd_data_hs++;
  $display("3.  ->  [  OK  ] DATA handshake at \t\t%0tns", $time/100);
end
else begin
  total_rd_data_hs++;
  $display("3.  ->  [FAILED] DATA handshake");
end
// -------------------------------------------


// ----------------- [RRESP] -----------------
int pass_read_resp, total_read_resp;

property read_resp_op_p_1;
  @(posedge clk) disable iff(!rst_n)
  ($rose(RLAST) && RRESP[1] == 1'b0) |-> ##1 (HRESP == 1'b0 && HREADY == 1'b1);
endproperty

read_resp_check_1: assert property(read_resp_op_p_1) begin
  pass_read_resp++;     total_read_resp++;
  $display("4.  ->  [  OK  ] RESP mapped at \t\t%0tns", $time/100);
end
else begin
  total_read_resp++;
  $display("4.  ->  [FAILED] RESP mapped");
end

property read_resp_op_p_2;
  @(posedge clk) disable iff(!rst_n)
  ($rose(RLAST) && RRESP[1] == 1'b1) |-> ##1 (HRESP == 1'b1 && HREADY == 1'b0);
endproperty

read_resp_check_2: assert property(read_resp_op_p_2) begin
  pass_read_resp++;     total_read_resp++;
  $display("4.  ->  [  OK  ] RESP mapped at \t\t%0tns", $time/100);
end
else begin
  total_read_resp++;
  $display("4.  ->  [FAILED] RESP mapped");
end
// -------------------------------------------


// ---------------- [ERROR] ------------------
property read_err_p;
@(posedge clk) disable iff(!rst_n)
((RRESP == SLVERR || RRESP == DECERR) && RVALID && RREADY) |-> ##1(HREADY == 1'b0) |-> ##1(HREADY == 1'b1);
endproperty

read_err_check: assert property(read_err_p) begin
  $display("4.  ->  [  OK  ] ERR_RESPONSE mapped at %0tns", $time/100);
end
else begin
  $display("4.  ->  [FAILED] ERR_RESPONSE mapped");
end
// -------------------------------------------
