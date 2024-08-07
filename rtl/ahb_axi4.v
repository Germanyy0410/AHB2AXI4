`timescale 1ns / 1ps

module ahb_axi4 #(
  // HBURST
  parameter SINGLE          = 3'b000,
  parameter INCR            = 3'b001,
  parameter WRAP4           = 3'b010,
  parameter INCR4           = 3'b011,
  parameter WRAP8           = 3'b100,
  parameter INCR8           = 3'b101,
  parameter WRAP16          = 3'b110,
  parameter INCR16          = 3'b111,

  // HTRANS
  parameter IDLE            = 2'b00,
  parameter BUSY            = 2'b01,
  parameter NONSEQ          = 2'b10,
  parameter SEQ             = 2'b11,

  // AXI BURST
  parameter FIXED_AXI       = 2'b00,
  parameter INCR_AXI        = 2'b01,
  parameter WRAP_AXI        = 2'b10,
  parameter RESERVED_AXI    = 2'b11,

  // AXI4 Response signals
  parameter OKAY            = 2'b00,
  parameter EXOKAY          = 2'b01,
  parameter SLVERR          = 2'b10,
  parameter DECERR          = 2'b11,

  // Configurable settings
  parameter ADDR_WIDTH      = 8,
  parameter DATA_WIDTH      = 8,
  parameter AWID_WIDTH      = 3,
  parameter BID_WIDTH       = 3,
  parameter ARID_WIDTH      = 3,
  parameter RID_WIDTH       = 3,

  parameter WRITE           = 0,
  parameter READ            = 1
)(
  input  wire                         clk         ,
  input  wire                         rst_n       ,

  // --------------------- AHB ---------------------
  input wire                          HWRITE      ,
  input wire    [1:0]                 HTRANS      ,
  input wire    [2:0]                 HSIZE       ,
  input wire    [2:0]                 HBURST      ,
  input wire    [ADDR_WIDTH-1:0]      HADDR       ,
  input wire    [DATA_WIDTH-1:0]      HWDATA      ,

  output reg                          HREADY      ,
  output reg    [DATA_WIDTH-1:0]      HRDATA      ,
  output reg                          HRESP       ,
  // -----------------------------------------------


  //----------------- AXI4 - Write -----------------
  input wire                          AWREADY     ,
  input wire                          WREADY      ,
  input wire                          BVALID      ,
  input wire    [1:0]                 BRESP       ,

  output reg    [AWID_WIDTH-1:0]      AWID        ,
  output reg    [ADDR_WIDTH-1:0]      AWADDR      ,
  output reg    [7:0]                 AWLEN       ,
  output reg    [2:0]                 AWSIZE      ,
  output reg    [1:0]                 AWBURST     ,
  output reg                          AWVALID     ,
  output reg    [DATA_WIDTH-1:0]      WDATA       ,
  output reg                          WVALID      ,
  output reg    [BID_WIDTH-1:0]       BID         ,
  output reg                          BREADY      ,
  output reg                          WLAST       ,
  // -----------------------------------------------


  //----------------- AXI4 - Read ------------------
  input wire                          ARREADY     ,
  input wire    [DATA_WIDTH-1:0]      RDATA       ,
  input wire                          RVALID      ,
  input wire                          RLAST       ,
  input wire    [RID_WIDTH-1:0]       RID         ,
  input wire    [1:0]                 RRESP       ,

  output reg    [ARID_WIDTH-1:0]      ARID        ,
  output reg    [ADDR_WIDTH-1:0]      ARADDR      ,
  output reg    [7:0]                 ARLEN       ,
  output reg    [2:0]                 ARSIZE      ,
  output reg    [1:0]                 ARBURST     ,
  output reg                          ARVALID     ,
  output reg                          RREADY      ,
  // -----------------------------------------------

  output reg                ff_wr_valid   [1:0]   ,
  output reg                ff_rd_valid   [1:0]   ,
  output reg    [7:0]       transfer_cnt
);

  // ------------------- flag -------------------
  reg   [DATA_WIDTH-1:0]    wr_data_last      ;
  reg                       flag_wr_data_last ;
  reg                       flag_wvalid       ;
  reg                       flag_wvalid_next  ;
  // --------------------------------------------


  // ------------------- FIFO -------------------
  reg   [DATA_WIDTH-1:0]    data_i            [1:0];
  reg   [DATA_WIDTH-1:0]    data_o            [1:0];

  reg                       ff_full           [1:0];
  reg                       ff_almost_full    [1:0];
  reg                       ff_empty          [1:0];
  reg                       ff_almost_empty   [1:0];
  // --------------------------------------------


  // ---------------- Instances -----------------
  ahb_axi4_fifo #(
    .DATA_WIDTH        (DATA_WIDTH),
    .FIFO_DEPTH        (256)
  ) u_wr_fifo (
    .clk               (clk),
    .rst_n             (rst_n),
    .data_i            (data_i[WRITE]),
    .data_o            (data_o[WRITE]),
    .wr_valid_i        (ff_wr_valid[WRITE]),
    .rd_valid_i        (ff_rd_valid[WRITE]),
    .almost_empty_o    (ff_almost_empty[WRITE]),
    .empty_o           (ff_empty[WRITE]),
    .almost_full_o     (ff_almost_full[WRITE]),
    .full_o            (ff_full[WRITE])
  );

  ahb_axi4_fifo #(
    .DATA_WIDTH        (DATA_WIDTH),
    .FIFO_DEPTH        (256)
  ) u_rd_fifo (
    .clk               (clk),
    .rst_n             (rst_n),
    .data_i            (data_i[READ]),
    .data_o            (data_o[READ]),
    .wr_valid_i        (ff_wr_valid[READ]),
    .rd_valid_i        (ff_rd_valid[READ]),
    .almost_empty_o    (ff_almost_empty[READ]),
    .empty_o           (ff_empty[READ]),
    .almost_full_o     (ff_almost_full[READ]),
    .full_o            (ff_full[READ])
  );

  burst_logic u_burst_logic (
    .clk        (clk),
    .rst_n      (rst_n),
    .HBURST     (HBURST),
    .HREADY     (HREADY),
    .HTRANS     (HTRANS),
    .HSIZE      (HSIZE),
    .AWSIZE     (AWSIZE),
    .ARSIZE     (ARSIZE),
    .AWBURST    (AWBURST),
    .ARBURST    (ARBURST),
    .AWLEN      (AWLEN),
    .ARLEN      (ARLEN)
  );
  // ----------------------------------------------

  assign AWID = 0;
  assign ARID = 0;

  // ---------------- transfer_cnt ----------------
  wire                      transfer_cnt_rst      ;
  reg   [7:0]               transfer_cnt_next     ;
  reg                       aw_handshake_en       ;
  reg                       aw_handshake_en_next  ;
  reg                       rd_last_transfer      ;
  reg                       rd_last_transfer_next ;

  assign transfer_cnt_rst = ((HTRANS == NONSEQ) && BVALID && BREADY && HWRITE) || ((HTRANS == NONSEQ) && ~HWRITE && HREADY);

  always @(*) begin
    transfer_cnt_next = transfer_cnt;

    if (transfer_cnt_rst) begin
      transfer_cnt_next = 0;
    end
    else if (aw_handshake_en && HREADY && (HTRANS != BUSY) && HWRITE) begin
      transfer_cnt_next = transfer_cnt + 1;
    end
    else if (RVALID && RREADY && HREADY && (HTRANS != BUSY) && (~HWRITE)) begin
      transfer_cnt_next = transfer_cnt + 1;
    end
  end

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      transfer_cnt <= 0;
    end
    else begin
      transfer_cnt <= transfer_cnt_next;
    end
  end
  // ----------------------------------------------

  //---------------- [rresp_hold] -----------------
  reg [1:0] rresp_h           ;
  reg [1:0] rresp_h_next      ;

  always @(*) begin
    rresp_h_next = rresp_h;
    if (RLAST && RVALID && RREADY && (HTRANS != NONSEQ)) begin
      rresp_h_next = RRESP;
    end
  end

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      rresp_h <= 2'b00;
    end
    else begin
      rresp_h <= rresp_h_next;
    end
  end
  // ----------------------------------------------


  // ------------------ [HREADY] ------------------
  // -- wire
  wire      BRESP_to_HREADY       ;
  wire      error_response        ;
  wire      wr_wait_state_en      ;
  wire      wr_wait_state_single  ;
  wire      wr_wait_state_burst   ;
  wire      rd_wait_state_en      ;
  wire      rd_wait_state_single  ;
  wire      rd_wait_state_burst   ;

  // -- reg
  reg       flag_error        ;
  reg       flag_error_next   ;
  reg       hready_next       ;

  assign BRESP_to_HREADY  = ~BRESP[1];
  assign RRESP_to_HREADY  = ~rresp_h_next[1];
  assign error_response   = (((BRESP[1]) || (rresp_h_next[1])) && (~HREADY));

  assign wr_wait_state_single = HWRITE && ((HTRANS == NONSEQ) && (HBURST == SINGLE) && HREADY);
  assign wr_wait_state_burst  = (HWRITE && ((HBURST != SINGLE) && (transfer_cnt >= AWLEN - 1) && (~BVALID))) || ff_full[WRITE];
  assign wr_wait_state_en     = wr_wait_state_single || wr_wait_state_burst;

  assign rd_wait_state_single = (~HWRITE) && ((HTRANS == NONSEQ) && (HBURST == SINGLE) && HREADY);
  assign rd_wait_state_burst  = (~HWRITE) && ((HBURST != SINGLE) && ((HTRANS == NONSEQ && HREADY) || (HTRANS == SEQ && HREADY && ff_empty[READ])));
  assign rd_wait_state_en     = rd_wait_state_single || rd_wait_state_burst;

  always @(*) begin
    hready_next = HREADY;

    if (HTRANS == IDLE) begin
      hready_next = 1'b1;
    end
    else if (flag_error_next) begin
      hready_next = 1'b1;
    end
    else if (wr_wait_state_en) begin
      hready_next = 1'b0;
    end
    else if (BVALID) begin
      hready_next = BRESP_to_HREADY;
    end
    else if (rd_wait_state_en) begin
      hready_next = 1'b0;
    end
    else if (rd_last_transfer && (~flag_error_next)) begin
      hready_next = RRESP_to_HREADY;
    end
    else if (~ff_empty[READ]) begin
      hready_next = 1'b1;
    end
  end

  always @(*) begin
    flag_error_next = flag_error;
    if (error_response) begin
      flag_error_next = 1'b1;
    end
    if (flag_error == 1'b1) begin
      flag_error_next = 1'b0;
    end
  end
  // ----------------------------------------------


  //--------------------- [AW] --------------------
  wire                    wr_addr_en;
  wire                    disable_awvalid;
  reg                     w_handshake_en;
  reg                     w_handshake_en_next;
  reg  [ADDR_WIDTH-1:0]   awaddr_next;
  reg                     awvalid_next;

  assign wr_addr_en       = (((HTRANS == NONSEQ) && HREADY && HWRITE) || (BVALID && BREADY && BRESP[1] == 1'b0));
  assign disable_awvalid  = (wr_wait_state_en && (AWVALID)) || (AWVALID && AWREADY);

  // -- AWADDR
  always @(*) begin
    awaddr_next = AWADDR;
    if (wr_addr_en) awaddr_next = HADDR;
  end

  // -- AWVALID
  always @(*) begin
    awvalid_next = AWVALID;
    if (disable_awvalid) awvalid_next = 1'b0;
    else if (wr_addr_en) awvalid_next = 1'b1;
  end

  // -- aw_handshake_en && w_handshake_en
  always @(*) begin
    aw_handshake_en_next = aw_handshake_en;
    w_handshake_en_next  = w_handshake_en;

    if (AWVALID && AWREADY) begin
      aw_handshake_en_next  = 1'b1;
      w_handshake_en_next   = 1'b1;
    end
    else if (BVALID && BREADY) begin
      aw_handshake_en_next  = 1'b0;
      w_handshake_en_next   = 1'b0;
    end
  end
  // ----------------------------------------------


  // -------------- [axi_wr_data_cnt] -------------
  reg [3:0] axi_wr_data_cnt;
  reg [3:0] axi_wr_data_cnt_next;

  always @(*) begin
    axi_wr_data_cnt_next = axi_wr_data_cnt;

    if (axi_wr_data_cnt == AWLEN + 1) begin
      axi_wr_data_cnt_next = 0;
    end
    else if (ff_rd_valid[WRITE]) begin
      axi_wr_data_cnt_next = axi_wr_data_cnt + 1;
    end
  end
  // ----------------------------------------------


  //------------- [wr_hold_last_data] -------------
  reg wr_hold_last_data;
  reg wr_hold_last_data_next;

  always @(*) begin
    wr_hold_last_data_next = wr_hold_last_data;

    if (HTRANS == NONSEQ && ~HREADY) begin
        wr_hold_last_data_next = 1'b0;
      end
      else begin
        wr_hold_last_data_next = 1'b1;
      end
  end
  // ----------------------------------------------


  // -------------------- [W] ---------------------
  reg   [DATA_WIDTH-1:0]    wdata_next;
  reg                       wvalid_next;
  reg                       wlast_next;
  reg                       bready_next;
  // -- AHB
  assign data_i[WRITE]       = HWDATA;
  assign ff_wr_valid[WRITE]  = (HWRITE && (~ff_full[WRITE]) && (HTRANS != BUSY) && aw_handshake_en && wr_hold_last_data) ? 1'b1 : 1'b0;

  // -- AXI4
  assign ff_rd_valid[WRITE]  = (WREADY && (~ff_empty[WRITE])) ? 1'b1 : 1'b0;

  // -- -- WDATA
  always @(*) begin
    wdata_next = WDATA;
    if (HBURST == SINGLE) wdata_next = HWDATA;
    else wdata_next = data_o[WRITE];
  end

    // -- -- WVALID
  always @(*) begin
    wvalid_next = WVALID;
    flag_wvalid_next = flag_wvalid;

    if (HBURST == SINGLE) begin
      if (WVALID && WREADY) begin
        wvalid_next = 1'b0;
      end
      else if (HREADY && (~flag_wvalid)) begin
        flag_wvalid_next = 1'b1;
      end
      else if (flag_wvalid) begin
        wvalid_next = 1'b1;
        flag_wvalid_next = 1'b0;
      end
    end
    else begin
      if (ff_full[WRITE] || ff_empty[WRITE] || axi_wr_data_cnt == AWLEN + 1) begin
          wvalid_next = 1'b0;
        end
        else if (~ff_empty[WRITE]) begin
          wvalid_next = 1'b1;
        end
    end
  end

  // -- -- WLAST
  always @(*) begin
    wlast_next = WLAST;

    if (HBURST == SINGLE) begin
      wlast_next = 1'b1;
    end
    else if (HBURST != SINGLE) begin
      if (axi_wr_data_cnt == AWLEN) begin
        wlast_next = 1'b1;
      end
      else if (((HTRANS == NONSEQ) && HREADY) || (~HWRITE) || (WLAST && WVALID && WREADY)) begin
        wlast_next = 1'b0;
      end
    end
  end

  // -- -- BREADY
  always @(*) begin
    bready_next = BREADY;

    if ((WDATA == wr_data_last) && WLAST && (~flag_wr_data_last) && aw_handshake_en && w_handshake_en && transfer_cnt == AWLEN) begin
        bready_next = 1'b1;
      end
      else if (BREADY && BVALID) begin
        bready_next = 1'b0;
      end
  end
  // ----------------------------------------------


  // --------------- [wr_data_last] ---------------
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      wr_data_last <= {DATA_WIDTH{1'b0}};
    end
    else begin
      if (((HBURST != SINGLE) && (HTRANS == NONSEQ) && (~BVALID)) ||
          ((HBURST == SINGLE) && (~BVALID))) begin
        wr_data_last <= HWDATA;
      end
    end
  end

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      flag_wr_data_last <= 1'b0;
    end
    else begin
      if ((WDATA == wr_data_last) && WLAST && (~flag_wr_data_last) && aw_handshake_en && w_handshake_en && transfer_cnt == AWLEN) begin
        flag_wr_data_last <= 1'b1;
      end
      else if (HWDATA != wr_data_last) begin
        flag_wr_data_last <= 1'b0;
      end
    end
  end
  // ----------------------------------------------


  // ------------------ [HRESP] -------------------
  reg hresp_next;

  assign BRESP_to_HRESP = (HWRITE && BVALID) ? BRESP[1] : 1'b0;
  assign RRESP_to_HRESP = ((~HWRITE) && RLAST) ? RRESP[1] : 1'b0;

  always @(*) begin
    hresp_next = HRESP;

    if (HWRITE && BVALID) begin
        hresp_next = BRESP_to_HRESP;
      end
      else if ((~HWRITE) && RLAST) begin
        hresp_next = RRESP_to_HRESP;
      end
      else begin
        hresp_next = 1'b0;
      end
  end
  // ----------------------------------------------


  // ------------------- [AR] ---------------------
  reg ar_handshake_en;
  reg ar_handshake_en_next;
  reg [ADDR_WIDTH-1:0] araddr_next;
  reg arvalid_next;

  assign rd_addr_en = (((HTRANS == NONSEQ) && HREADY && ~HWRITE) || (RREADY && RVALID && RLAST && (~rresp_h[1] || ~RRESP[1])));

  // -- ARADDR
  always @(*) begin
    araddr_next = ARADDR;
    if (rd_addr_en) ARADDR <= HADDR;
  end

  // -- ARVALID
  always @(*) begin
    arvalid_next = ARVALID;

    if (ARVALID && ARREADY) begin
      arvalid_next = 1'b0;
    end
    else if (rd_addr_en) begin
      arvalid_next = 1'b1;
    end
    else if (rd_wait_state_en) begin
      arvalid_next = 1'b0;
    end
  end

  // -- ar_handshake_en
  always @(*) begin
    ar_handshake_en_next = ar_handshake_en;

    if (ARVALID && ARREADY) begin
      ar_handshake_en_next = 1'b1;
    end
    else if (HTRANS == NONSEQ && HREADY && (~HWRITE)) begin
      ar_handshake_en_next = 1'b0;
    end
  end
  // ----------------------------------------------


  // ------------------- [R] ----------------------
  reg [DATA_WIDTH-1:0] hrdata_next;
  reg rready_next;

  // -- AXI4
  assign data_i[READ]       = RDATA;
  assign ff_wr_valid[READ]  = ((~HWRITE) && (~ff_full[READ]) && RVALID) ? 1'b1 : 1'b0;

  // -- AHB
  assign ff_rd_valid[READ]  = ((~ff_empty[READ]) && (HTRANS != BUSY)) ? 1'b1 : 1'b0;

  // -- -- HRDATA
  always @(*) begin
    hrdata_next = HRDATA;

    if (HBURST == SINGLE) hrdata_next = RDATA;
    else hrdata_next = data_o[READ];
  end

  // -- -- RREADY
  always @(*) begin
    rready_next = RREADY;
    if (HBURST == SINGLE) begin
      if (RREADY && RVALID) begin
        rready_next <= 1'b0;
      end
      else if (ARVALID && ARREADY) begin
        rready_next <= 1'b1;
      end
    end
    else begin
      if (ff_full[READ]) begin
        rready_next <= 1'b0;
      end
      else if (HTRANS == NONSEQ) begin
        rready_next <= 1'b1;
      end
    end
  end

  always @(*) begin
    rd_last_transfer_next = rd_last_transfer;

    if ((~HWRITE) && (HBURST != SINGLE) && (transfer_cnt == ARLEN - 1) && HREADY) begin
      rd_last_transfer_next = 1'b1;
    end
    else if (ARREADY && ARVALID) begin
      rd_last_transfer_next = 1'b0;
    end
    else if (HBURST == SINGLE && RVALID && RREADY) begin
      rd_last_transfer_next = 1'b1;
    end
  end
  // ----------------------------------------------

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      HREADY            <= 1'b1;
      flag_error        <= 1'b0;

      AWADDR            <= {ADDR_WIDTH{1'b0}};
      AWVALID           <= 1'b0;
      aw_handshake_en   <= 1'b0;
      w_handshake_en    <= 1'b0;
      axi_wr_data_cnt   <= 0;

      WDATA             <= {DATA_WIDTH{1'b0}};
      WVALID            <= 1'b0;
      flag_wvalid       <= 1'b0;
      wr_hold_last_data <= 1'b1;
      WLAST             <= 1'b0;

      BREADY            <= 1'b0;
      HRESP             <= 1'b0;

      ARADDR            <= {ADDR_WIDTH{1'b0}};
      ARVALID           <= 1'b0;
      ar_handshake_en   <= 1'b0;

      HRDATA            <= {DATA_WIDTH{1'b0}};
      RREADY            <= 1'b0;
      rd_last_transfer  <= 1'b0;
    end
    else begin
      HREADY            <= hready_next;
      flag_error        <= flag_error_next;

      AWADDR            <= awaddr_next;
      AWVALID           <= awvalid_next;
      aw_handshake_en   <= aw_handshake_en_next;
      w_handshake_en    <= w_handshake_en_next;
      axi_wr_data_cnt   <= axi_wr_data_cnt_next;

      WDATA             <= wdata_next;
      WVALID            <= wvalid_next;
      flag_wvalid       <= flag_wvalid_next;
      wr_hold_last_data <= wr_hold_last_data_next;
      WLAST             <= wlast_next;

      BREADY            <= bready_next;
      HRESP             <= hresp_next;

      ARADDR            <= araddr_next;
      ARVALID           <= arvalid_next;
      ar_handshake_en   <= ar_handshake_en_next;

      HRDATA            <= hrdata_next;
      RREADY            <= rready_next;
      rd_last_transfer  <= rd_last_transfer_next;
    end
  end
endmodule
