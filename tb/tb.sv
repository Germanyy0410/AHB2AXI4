`timescale 1ns/1ps

`define DEBUG 1000

`define WRITE_SINGLE_TRANSACTION            3'b000
`define WRITE_BURST_TRANSACTION             3'b001
`define WRITE_BURST_TERMINATE_TRANSACTION   3'b010

`define READ_SINGLE_TRANSACTION             3'b011
`define READ_BURST_TRANSACTION              3'b100

`define N_OF_TEST               1
`define N_OF_TRANS              12

`define ADDR_WIDTH              32
`define DATA_WIDTH              32

`define AWREADY_MAX_WAIT        3
`define WREADY_MAX_WAIT         3
`define BVALID_MAX_WAIT         2
`define ARREADY_MAX_WAIT        3
`define RVALID_MAX_WAIT         5
`define BUSY_MAX_HOLD           3

typedef enum logic [1:0] {
  IDLE    = 2'b00,
  BUSY    = 2'b01,
  NONSEQ  = 2'b10,
  SEQ     = 2'b11
} HTRANS_t;

typedef enum logic [3:0] {
  IDLE_fsm   = 4'b0000,
  WR_ADDR    = 4'b0001,
  WR_DATA    = 4'b0010,
  WR_NEXT    = 4'b0011,
  WR_RESP    = 4'b0100,
  RD_ADDR    = 4'b0101,
  RD_WAIT    = 4'b0110,
  RD_DATA    = 4'b0111,
  RD_DONE    = 4'b1000
} state_t;

typedef enum logic [1:0] {
  OK      = 2'b00,
  ERR     = 2'b10,
  PENDING = 2'b01
} resp_t;

class ahb_axi4_transaction #(int mode = `WRITE_SINGLE_TRANSACTION);
  rand bit [`ADDR_WIDTH-1:0]  HADDR ;
  rand bit [`DATA_WIDTH-1:0]  HWDATA;
  rand bit [`DATA_WIDTH-1:0]  RDATA ;
  rand bit [1:0]              BRESP ;
  rand bit [1:0]              RRESP ;
  rand bit [`ADDR_WIDTH-1:0]  HRAND ;

  rand int                    AWREADY_wait  ;
  rand int                    WREADY_wait   ;
  rand int                    BVALID_wait   ;
  rand int                    ARREADY_wait  ;
  rand int                    RVALID_wait   ;
  rand int                    busy_hold_time;

  constraint slv_delay {
    AWREADY_wait >= 1                 ;
    AWREADY_wait <= `AWREADY_MAX_WAIT ;
    WREADY_wait  >= 1                 ;
    WREADY_wait  <= `WREADY_MAX_WAIT  ;
    BVALID_wait  >= 1                 ;
    BVALID_wait  <= `BVALID_MAX_WAIT  ;

    ARREADY_wait >= 1                 ;
    ARREADY_wait <= `ARREADY_MAX_WAIT ;
    RVALID_wait  >= 1                 ;
    RVALID_wait  <= `RVALID_MAX_WAIT  ;

    busy_hold_time >= 1               ;
    busy_hold_time <= `BUSY_MAX_HOLD  ;
  }

  constraint ahb_axi4_cntr {
    if (mode == `WRITE_SINGLE_TRANSACTION) {
      BRESP dist {2'b00 :/ 2, 2'b01 :/ 0, 2'b10 :/ 0, 2'b11 :/ 0};
    }
    else if (mode == `READ_SINGLE_TRANSACTION) {
      RRESP dist {2'b00 :/ 1, 2'b01 :/ 0, 2'b10 :/ 0, 2'b11 :/ 0};
    }
  }
endclass

module ahb_axi4_tb #(
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
  parameter PENDING         = 2'b01,
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
)();
  reg                       clk       ;
  reg                       rst_n     ;
  wire                      flag_error;

  reg                       HWRITE    ;

  HTRANS_t                  HTRANS    ;

  reg   [2:0]               HSIZE     ;
  reg   [2:0]               HBURST    ;
  reg   [ADDR_WIDTH-1:0]    HADDR     ;
  reg   [DATA_WIDTH-1:0]    HWDATA    ;

  wire                      HREADY    ;
  wire  [DATA_WIDTH-1:0]    HRDATA    ;
  wire                      HRESP     ;

  reg                       AWREADY   ;
  reg                       WREADY    ;
  reg                       BVALID    ;
  resp_t                    BRESP     ;

  wire  [AWID_WIDTH-1:0]    AWID      ;
  wire  [ADDR_WIDTH-1:0]    AWADDR    ;
  wire  [7:0]               AWLEN     ;
  wire  [2:0]               AWSIZE    ;
  wire  [1:0]               AWBURST   ;
  wire                      AWVALID   ;
  wire  [DATA_WIDTH-1:0]    WDATA     ;
  wire                      WVALID    ;
  wire                      WLAST     ;
  wire                      BREADY    ;

  reg                       ARREADY   ;
  reg   [DATA_WIDTH-1:0]    RDATA     ;
  reg                       RVALID    ;
  reg                       RLAST     ;
  reg   [RID_WIDTH-1:0]     RID       ;
  resp_t                    RRESP     ;

  wire  [ARID_WIDTH-1:0]    ARID      ;
  wire  [ADDR_WIDTH-1:0]    ARADDR    ;
  wire  [7:0]               ARLEN     ;
  wire  [2:0]               ARSIZE    ;
  wire  [1:0]               ARBURST   ;
  wire                      ARVALID   ;
  wire                      RREADY    ;

  reg   [7:0]       trans_no              ;
  wire              flag_busy             ;
  wire              flag_wr_data          ;
  wire              flag_busrt_terminate  ;
  wire  [7:0]       transfer_cnt          ;
  wire              ff_wr_valid     [1:0] ;
  wire              ff_rd_valid     [1:0] ;

  ahb_axi4 dut (
    .clk            (clk          ),
    .rst_n          (rst_n        ),

    // AHB
    .HWRITE         (HWRITE       ),
    .HREADY         (HREADY       ),
    .HTRANS         (HTRANS       ),
    .HSIZE          (HSIZE        ),
    .HBURST         (HBURST       ),
    .HADDR          (HADDR        ),
    .HWDATA         (HWDATA       ),
    .HRDATA         (HRDATA       ),
    .HRESP          (HRESP        ),

    // AXI4 [Write]
    .AWID           (AWID         ),
    .AWLEN          (AWLEN        ),
    .AWSIZE         (AWSIZE       ),
    .AWBURST        (AWBURST      ),

    // AXI4 [Write] - Addr
    .AWADDR         (AWADDR       ),
    .AWVALID        (AWVALID      ),
    .AWREADY        (AWREADY      ),

    // AXI4 [Write] - Data
    .WDATA          (WDATA        ),
    .WVALID         (WVALID       ),
    .WREADY         (WREADY       ),
    .WLAST          (WLAST        ),

    // AXI4 [Write] - Resp
    .BVALID         (BVALID       ),
    .BREADY         (BREADY       ),
    .BRESP          (BRESP        ),

    // AXI4 [Read]
    .ARID           (ARID         ),
    .ARLEN          (ARLEN        ),
    .ARSIZE         (ARSIZE       ),
    .ARBURST        (ARBURST      ),

    // AXI4 [Read] - Addr
    .ARADDR         (ARADDR       ),
    .ARVALID        (ARVALID      ),
    .ARREADY        (ARREADY      ),

    // AXI4 [Read] - Data
    .RID            (RID          ),
    .RDATA          (RDATA        ),
    .RVALID         (RVALID       ),
    .RREADY         (RREADY       ),
    .RLAST          (RLAST        ),
    .RRESP          (RRESP        ),

    .transfer_cnt   (transfer_cnt ),
    .ff_rd_valid    (ff_rd_valid  ),
    .ff_wr_valid    (ff_wr_valid  )

    );

  `ifdef DEBUG
    `include "sva/wr_check_point.sv"
    `include "sva/rd_check_point.sv"
    `include "helper.sv"
    // `include "write_task.sv"
    // `include "read_task.sv"
  `else
    `include "v2/check_point.sv"
    `include "v2/helper.sv"
  `endif

  ahb_axi4_transaction #(`WRITE_SINGLE_TRANSACTION) trans_0;
  ahb_axi4_transaction #(`READ_SINGLE_TRANSACTION)  trans_1;
  int rand_num_transfers;
  integer burst_length;
  bit [31:0] hold_addr;

  task READ_TASK(input [2:0] HBURST_config, input integer trans_num);
    trans_1 = new();
    HBURST  = HBURST_config;
    if (HBURST == SINGLE) begin
      burst_length = 1;
    end
    else if (HBURST == INCR4) begin
      burst_length = 4;
    end
    else if (HBURST == INCR) begin
      burst_length = 16;
    end

    for (int i = 0; i < burst_length; i++) begin
      assert (trans_1.randomize()) else $error("Randomization in READ_TASK failed");

      if (HBURST == SINGLE) begin
        if (trans_num == 0) begin
          HTRANS = IDLE;
          c1;
          HTRANS = NONSEQ;
          HWRITE = 1'b0;
          HADDR  = 4;
          ARREADY = 1'b1;
        end
        else begin
          c1;
          HTRANS = IDLE;
          c3;
          HTRANS = NONSEQ;
          HWRITE = 1'b0;

          hold_addr = HADDR;
          HADDR  = hold_addr + 1;

          repeat(trans_1.RVALID_wait) c1;
          RVALID = 1'b1;
          RDATA  = hold_addr;
          RLAST  = 1'b1;
          RRESP  = trans_1.RRESP;

          c1;
          RVALID = 1'b0;
          RLAST  = 1'b0;
        end
      end
      else if (HBURST == INCR4) begin
        if (i == 0) begin
          if (trans_num == 0) begin
            c3;
            HTRANS = NONSEQ;
            HWRITE = 1'b0;
            HADDR  = 4;
            c1;
            ARREADY = 1'b1;
            RLAST = 1'b0;
          end
          else begin
            HTRANS = NONSEQ;
            HWRITE = 1'b0;
            HADDR  = trans_1.HRAND & 32'hFFFF0000;

            RVALID = 1'b1;
            //RDATA  = hold_addr + 1;
            // RLAST  = 1'b1;
            // RRESP  = trans_1.RRESP;
            RVALID = 1'b0;
            RLAST  = 1'b0;
            c1;
          end
        end
        else begin
          HTRANS = IDLE;
          c3;
          // if (i == 1) HTRANS = BUSY;
          HTRANS = SEQ;

          hold_addr = HADDR;
          HADDR = HADDR + 1;

          c1;
          RVALID = 1'b1;
          if (i == 1) repeat(3) c1;

        end
      end


    end
  endtask

  task WRITE_TASK(input [2:0] HBURST_config, input integer trans_num, input integer num_transfers = 16);
    trans_0 = new();
    HBURST  = HBURST_config;

    if (HBURST == SINGLE) begin
      burst_length = 1;
    end
    else if (HBURST == INCR4) begin
      burst_length = 4;
    end
    else if (HBURST == INCR) begin
      burst_length = 16;
    end

    rand_num_transfers = $urandom_range(6, 4);

    for (integer i = 0; i < burst_length; i = i + 1) begin
      assert (trans_0.randomize()) else $error("Randomization in WRITE_TASK failed");

      if (HBURST == SINGLE) begin
        if (trans_num == 0) begin
          HTRANS = IDLE;
          BRESP  = PENDING;
          c1;
          HTRANS = NONSEQ;
          HWRITE = 1'b1;
          HADDR  = 4;
          AWREADY = 1'b1;
        end
        else begin
            c1;
            HTRANS = IDLE;
            BRESP  = PENDING;
            c3;
            HTRANS = NONSEQ;
            HWRITE = 1'b1;
            HWDATA = 4 + trans_num - 1;
            HADDR  = 4 + trans_num;

            c1;
            WREADY  = 1'b1;

            c1;
            BVALID  = 1'b1;
            BRESP   = trans_0.BRESP;

            repeat(1) c1;
            BVALID  = 1'b0;
        end
      end

      if (HBURST == INCR || HBURST == INCR4) begin
        if (i == 0) begin
          if (trans_num == 0) begin
            c1;
            HTRANS = IDLE;
            BRESP  = PENDING;
            repeat(1) c1;
            HTRANS = NONSEQ;
            HWRITE = 1'b1;
            HADDR  = 4;
            AWREADY = 1'b1;

            c1;
            HTRANS = BUSY;
            HADDR  = HADDR + 1;
            // HWDATA = 1;
            c1;
            HADDR  = HADDR - 1;
          end
          else begin
            c1;
            HTRANS = NONSEQ;
            BRESP  = PENDING;
            HWRITE = 1'b1;
            HWDATA = HADDR;
            HADDR  = 5;

            repeat(3) c1;
            BVALID  = 1'b1;
            BRESP   = trans_0.BRESP;

            c1;
            BVALID  = 1'b0;

            c1;
            HTRANS = BUSY;
            HADDR  = HADDR + 1;
            c1;
            HADDR  = HADDR - 1;
          end
        end

        else if (i < 4) begin
          if (i != 1) c1;
          WREADY = 1'b1;
          HTRANS = IDLE;
          c3;
          HTRANS = SEQ;
          BRESP  = PENDING;

          HWDATA = HADDR;
          HADDR = HADDR + 1;
        end
      end
    end
  endtask

  int which_test;
  int num_transactions;
  int num_transfers;
  int all_pass, all_total;
  string str[5] = {"WR_SINGLE", "WR_INCR4", "WR_INCR", "RD_SINGLE", "RD_BURST"};

  always #10 clk = ~clk;

  initial begin
    clk      = 1'b1;
    rst_n    = 1'b0;
    trans_no = 0;

    HTRANS  = IDLE;

    BRESP   = 0;
    AWREADY = 1'b0;
    WREADY  = 1'b0;
    BVALID  = 1'b0;

    ARREADY = 1'b0;
    RVALID  = 1'b0;
    RRESP   = 0;
    RLAST   = 1'b0;

    #12 rst_n = 1'b1;
    HWRITE  = 1'b0;
    #8;

    for (int i = 0; i < `N_OF_TEST; i++) begin
      integer seed0;
      num_transactions = $dist_uniform(seed0, 1, `N_OF_TRANS);

      $display("\n\n");
      $display("------------------------------------------------------------");
      $display("|             Test %d of %d              |", i, `N_OF_TEST);
      $display("------------------------------------------------------------\n");

      for (int j = 0; j < num_transactions; j++) begin
        integer seed1;
        trans_no += 1;

        which_test = `WRITE_SINGLE_TRANSACTION;
        // which_test = $dist_uniform(seed1, 0, 4);

        $display("\n============= %s Transaction, ID = %0d ================", str[which_test], j + 1);

        case (which_test)
          `WRITE_SINGLE_TRANSACTION: begin
            WRITE_TASK(SINGLE, j);
            num_transfers += 1;
          end

          `WRITE_BURST_TRANSACTION: begin
            WRITE_TASK(INCR4, j);
            num_transfers += 4;
          end


          `READ_SINGLE_TRANSACTION: begin
            READ_TASK(SINGLE, j);
            num_transfers += 1;
          end

          `READ_BURST_TRANSACTION: begin
            READ_TASK(INCR4, j);
            num_transfers += 4;
          end

          default: begin
            WRITE_TASK(SINGLE, j);
            num_transfers += 1;
          end
        endcase

        $display("============================================================\n");
      end
      HTRANS = IDLE;
      all_pass  += pass_write_addr + pass_write_data + pass_write_resp + pass_read_addr + pass_read_data + pass_read_resp + pass_transfer_cnt;
      all_total += total_write_addr + total_write_data + total_write_resp + total_read_addr + total_read_data + total_read_resp + total_transfer_cnt;

      $display("\n\n");
      $display("------------------------------------------------------------");
      $display("|                     REPORT SUMMARY                       |");
      $display("------------------------------------------------------------");

      $display("\n Total transactions = %0d\t\tTotal transfers = %0d\n", num_transactions - 1, num_transfers - 1);
      $display("------------------------------------------------------------");

      // $display("  -  RESET     :                  %2d | %2d", pass_rst, total_rst);
      // $display("\n------------------------------------------------------------");

      $display("Write transaction test:");
      $display("     - transfer_cnt :                  %2d | %2d", pass_transfer_cnt, total_transfer_cnt);
      $display("\n     ADDRESS                                  ");
      $display("     - mapped       :                  %2d | %2d", pass_write_addr, total_write_addr);
      $display("     - handshake    :                  %2d | %2d", pass_wr_addr_hs, total_wr_addr_hs);

      $display("\n     DATA                                     ");
      $display("     - mapped       :                  %2d | %2d", pass_write_data, total_write_data);
      $display("     - handshake    :                  %2d | %2d", pass_wr_data_hs, total_wr_data_hs);

      $display("\n     RESPONSE                                 ");
      $display("     - mapped       :                  %2d | %2d", pass_write_resp, total_write_resp);
      $display("     - handshake    :                  %2d | %2d", pass_wr_resp_hs, total_wr_resp_hs);
      $display("\n");
      $display("------------------------------------------------------------");

      $display("Read transaction test:");
      $display("     ADDRESS                                  ");
      $display("     - mapped       :                  %2d | %2d", pass_read_addr, total_read_addr);
      $display("     - handshake    :                  %2d | %2d", pass_rd_addr_hs, total_rd_addr_hs);

      $display("     DATA                                     ");
      $display("     - mapped       :                  %2d | %2d", pass_read_data, total_read_data);
      $display("     - handshake    :                  %2d | %2d", pass_rd_data_hs, total_rd_data_hs);

      $display("     RESPONSE                                 ");
      $display("     - mapped       :                  %2d | %2d", pass_read_resp, total_read_resp);

      $display("\n");

      $display("------------------------------------------------------------");
      $display("Summary:");
      $display("     Total items checked  :            %2d | %2d", all_pass, all_total);
      $display("     Overall              :             %0.1f%%", 100*(all_pass)/(all_total));
      $display("\n------------------------------------------------------------");
      $display("|                           END                            |");
      $display("------------------------------------------------------------\n\n\n");
    end
  end

  initial begin
      #50000;
      $display("\n\n");
      $finish();
  end

  // initial begin
  //   #60.1;
  //   RDATA = 1;
  //   #20.1;
  //   RDATA = 2;
  //   #20.1;
  //   RDATA = 3;
  //   #20.1;
  //   RDATA = 4;
  //   RLAST = 1;
  //   RRESP = 2'b01;
  //   #20.1;
  //   RLAST = 0;
  //   #60.1;
  //   RDATA = 1;
  //   #20.1;
  //   RDATA = 2;
  //   #20.1;
  //   RDATA = 3;
  //   #20.1;
  //   RDATA = 4;
  // end

`ifndef DEBUG
  initial begin
    $fsdbDumpfile("dump.fsdb");
    $fsdbDumpvars;
  end
`endif
endmodule

