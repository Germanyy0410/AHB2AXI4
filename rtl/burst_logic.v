`timescale 1ns / 1ps

module burst_logic #(
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
  input wire           clk     ,
  input wire           rst_n   ,
  input wire  [2:0]    HBURST  ,
  input wire  [2:0]    HSIZE   ,
  input wire           HREADY  ,
  input wire  [1:0]    HTRANS  ,

  output reg  [2:0]    AWSIZE  ,
  output reg  [2:0]    ARSIZE  ,
  output reg  [1:0]    AWBURST ,
  output reg  [1:0]    ARBURST ,
  output reg  [7:0]    AWLEN   ,
  output reg  [7:0]    ARLEN
);
  reg  [1:0]  AWBURST_next ;
  reg  [1:0]  ARBURST_next ;
  reg  [7:0]  AWLEN_next   ;
  reg  [7:0]  ARLEN_next   ;

  wire HBURST_to_AxBURST_SINGLE   = (HBURST == SINGLE);
  wire HBURST_to_AxBURST_INCR     = (HBURST == INCR) || (HBURST == INCR4) || (HBURST == INCR8) || (HBURST == INCR16);
  wire HBURST_to_AxBURST_WRAP     = (HBURST == WRAP4) || (HBURST == WRAP8) || (HBURST == WRAP16);
  wire HBURST_to_AxLEN_undefined  = (HBURST == INCR);
  wire HBURST_to_AxLEN_1          = (HBURST == SINGLE);
  wire HBURST_to_AxLEN_4          = (HBURST == INCR4) || (HBURST == WRAP4);
  wire HBURST_to_AxLEN_8          = (HBURST == INCR8) || (HBURST == WRAP8);
  wire HBURST_to_AxLEN_16         = (HBURST == INCR16) || (HBURST == WRAP16);

  always @(*) begin
    AWBURST_next = RESERVED_AXI;
    ARBURST_next = RESERVED_AXI;
    AWLEN_next   = 8'b00000000;
    ARLEN_next   = 8'b00000000;

    if (HREADY && HTRANS == NONSEQ) begin
      if (HBURST_to_AxBURST_SINGLE) begin
      AWBURST_next = FIXED_AXI;
      ARBURST_next = FIXED_AXI;
    end else if (HBURST_to_AxBURST_INCR) begin
      AWBURST_next = INCR_AXI;
      ARBURST_next = INCR_AXI;
    end else if (HBURST_to_AxBURST_WRAP) begin
      AWBURST_next = WRAP_AXI;
      ARBURST_next = WRAP_AXI;
    end

    if (HBURST_to_AxLEN_1) begin
      AWLEN_next = 8'b00000000;
      ARLEN_next = 8'b00000000;
    end else if (HBURST_to_AxLEN_4) begin
      AWLEN_next = 8'b00000011;
      ARLEN_next = 8'b00000011;
    end else if (HBURST_to_AxLEN_8) begin
      AWLEN_next = 8'b00000111;
      ARLEN_next = 8'b00000111;
    end else if (HBURST_to_AxLEN_16 || HBURST_to_AxLEN_undefined) begin
      AWLEN_next = 8'b00001111;
      ARLEN_next = 8'b00001111;
    end
    end

  end

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      AWSIZE  <= 3'b000       ;
      AWBURST <= 2'b00        ;
      AWLEN   <= 8'b00000000  ;
      ARSIZE  <= 3'b000       ;
      ARBURST <= 2'b00        ;
      ARLEN   <= 8'b00000000  ;
    end else begin
      AWSIZE  <= HSIZE        ;
      AWBURST <= AWBURST_next ;
      AWLEN   <= AWLEN_next   ;
      ARSIZE  <= HSIZE        ;
      ARBURST <= ARBURST_next ;
      ARLEN   <= ARLEN_next   ;
    end
  end
endmodule
