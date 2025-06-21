`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company:
// Engineer: Xu Zhang (zhangxu415@mails.ucas.ac.cn)
//
// Create Date: 06/14/2018 11:39:09 AM
// Design Name:
// Module Name: dma_core
// Project Name:
// Target Devices:
// Tool Versions:
// Description:
//
// Dependencies:
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////


module engine_core #(
    parameter integer DATA_WIDTH = 32
) (
    input clk,
    input rst,

    output [31:0] src_base,
    output [31:0] dest_base,
    output [31:0] tail_ptr,
    output [31:0] head_ptr,
    output [31:0] dma_size,
    output [31:0] ctrl_stat,

    input [31:0] reg_wr_data,
    input [ 5:0] reg_wr_en,

    output intr,

    output [31:0] rd_req_addr,
    output [ 4:0] rd_req_len,
    output        rd_req_valid,

    input         rd_req_ready,
    input  [31:0] rd_rdata,
    input         rd_last,
    input         rd_valid,
    output        rd_ready,

    output [31:0] wr_req_addr,
    output [ 4:0] wr_req_len,
    output        wr_req_valid,
    input         wr_req_ready,
    output [31:0] wr_data,
    output        wr_valid,
    input         wr_ready,
    output        wr_last,

    output        fifo_rden,
    output [31:0] fifo_wdata,
    output        fifo_wen,

    input [31:0] fifo_rdata,
    input        fifo_is_empty,
    input        fifo_is_full
);
  // TODO: Please add your logic design here

  wire EN = ctrl_stat[0];
  assign intr = ctrl_stat[31];
  reg [2:0] current_state_RD, next_state_RD, current_state_WR, next_state_WR;
  wire rd_complete, wr_complete;

  localparam IDLE = 3'b000, RD_REQ = 3'b001, RD = 3'b010, WR_REQ = 3'b011, WR = 3'b100;

  // registers controlled by CPU
  reg [31:0] src_base_reg;
  reg [31:0] dest_base_reg;
  reg [31:0] tail_ptr_reg;
  reg [31:0] head_ptr_reg;
  reg [31:0] dma_size_reg;
  reg [31:0] ctrl_stat_reg;

  always @(posedge clk) begin
    if (rst) begin
      src_base_reg  <= 32'h0;
      dest_base_reg <= 32'h0;
      tail_ptr_reg  <= 32'h0;
      head_ptr_reg  <= 32'h0;
      dma_size_reg  <= 32'h0;
      ctrl_stat_reg <= 32'h1;
    end else if (|reg_wr_en[5:0]) begin
      if (reg_wr_en[0]) src_base_reg <= reg_wr_data;
      if (reg_wr_en[1]) dest_base_reg <= reg_wr_data;
      if (reg_wr_en[2]) tail_ptr_reg <= reg_wr_data;
      if (reg_wr_en[3]) head_ptr_reg <= reg_wr_data;
      if (reg_wr_en[4]) dma_size_reg <= reg_wr_data;
      if (reg_wr_en[5]) ctrl_stat_reg <= reg_wr_data;
    end else if ((current_state_WR == WR_REQ) && wr_complete) begin
      ctrl_stat_reg <= {1'b1, ctrl_stat_reg[30:0]};
      tail_ptr_reg  <= tail_ptr_reg + dma_size_reg;
      src_base_reg  <= src_base_reg;
      dest_base_reg <= dest_base_reg;
      head_ptr_reg  <= head_ptr_reg;
      dma_size_reg  <= dma_size_reg;
    end else begin
      ctrl_stat_reg <= ctrl_stat_reg;  // retain previous value
      src_base_reg  <= src_base_reg;
      dest_base_reg <= dest_base_reg;
      tail_ptr_reg  <= tail_ptr_reg;
      head_ptr_reg  <= head_ptr_reg;
      dma_size_reg  <= dma_size_reg;
    end
  end

  assign src_base  = src_base_reg;
  assign dest_base = dest_base_reg;
  assign tail_ptr  = tail_ptr_reg;
  assign head_ptr  = head_ptr_reg;
  assign dma_size  = dma_size_reg;
  assign ctrl_stat = ctrl_stat_reg;

  // FSM implementation
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      current_state_RD <= IDLE;
      current_state_WR <= IDLE;
    end else begin
      current_state_RD <= next_state_RD;
      current_state_WR <= next_state_WR;
    end
  end

  always @(*) begin
    next_state_RD = current_state_RD;
    next_state_WR = current_state_WR;

    case (current_state_RD)
      IDLE: begin
        if (EN && (tail_ptr != head_ptr) && (current_state_WR == IDLE)) begin
          next_state_RD = RD_REQ;
        end else begin
          next_state_RD = IDLE;
        end
      end
      RD_REQ: begin
        if (rd_req_ready && rd_req_valid) begin
          next_state_RD = RD;
        end else if (rd_complete) begin
          next_state_RD = IDLE;
        end else begin
          next_state_RD = RD_REQ;
        end
      end
      RD: begin
        if (rd_valid && rd_last && !fifo_is_full) begin
          next_state_RD = RD_REQ;
        end else begin
          next_state_RD = RD;
        end
      end
      default: begin
        next_state_RD = IDLE;  // Fallback to IDLE state
      end
    endcase

    case (current_state_WR)
      IDLE: begin
        if (EN && (tail_ptr != head_ptr) && (current_state_RD == IDLE)) begin
          next_state_WR = WR_REQ;
        end else begin
          next_state_WR = IDLE;
        end
      end
      WR_REQ: begin
        if (wr_req_ready && wr_req_valid) begin
          next_state_WR = WR;
        end else if (wr_complete) begin
          next_state_WR = IDLE;
        end else begin
          next_state_WR = WR_REQ;
        end
      end
      WR: begin
        if (wr_valid && wr_last) begin
          next_state_WR = WR_REQ;
        end else begin
          next_state_WR = WR;
        end
      end
      default: begin
        next_state_WR = IDLE;  // Fallback to IDLE state
      end
    endcase

  end

  reg [27:0] rd_counter;  // use 28 bits to count up to 256M
  reg [27:0] wr_counter;
  wire start_new_task = (current_state_RD == IDLE) && (current_state_WR == IDLE) && EN && (head_ptr != tail_ptr);

  always @(posedge clk) begin
    if (rst) begin
      rd_counter <= 28'h0;
      wr_counter <= 28'h0;
    end else if (start_new_task) begin
      rd_counter <= 28'h0;
      wr_counter <= 28'h0;
    end else begin
      if (current_state_RD == RD && rd_valid && rd_last && !fifo_is_full && rd_ready) begin
        rd_counter <= rd_counter + 1;
      end
      if (current_state_WR == WR && wr_valid && wr_last && wr_ready) begin
        wr_counter <= wr_counter + 1;
      end
    end
  end

  reg [2:0] wr_last_counter;

  always @(posedge clk) begin
    if (rst) begin
      wr_last_counter <= 3'b0;
    end else if ((current_state_WR == WR_REQ) && wr_req_ready && wr_req_valid) begin
      wr_last_counter <= wr_req_len;
    end else if (wr_valid && wr_ready) begin
      wr_last_counter <= wr_last_counter - 1;
    end else begin
      wr_last_counter <= wr_last_counter;
    end
  end

  wire [27:0] total_burst_num = dma_size[31:5] + (|dma_size[4:0]);
  wire [2:0] last_burst_len = dma_size[4:2] - {2'b0, !(|dma_size[1:0])};

  wire rd_complete = (rd_counter == total_burst_num) && (rd_counter != 0);
  wire wr_complete = (wr_counter == total_burst_num) && (wr_counter != 0);

  assign rd_req_addr = src_base + tail_ptr + {rd_counter, 5'b0};
  assign rd_req_len = (rd_counter == total_burst_num - 1) ? last_burst_len : 5'd7;
  assign rd_req_valid = (current_state_RD == RD_REQ) && fifo_is_empty && !rd_complete;
  assign rd_ready = (current_state_RD == RD) && !fifo_is_full;

  // helping signals for wr_signals
  reg last_fifo_rden;
  reg wr_valid_reg;
  reg [31:0] wr_data_reg;

  always @(posedge clk) begin
    last_fifo_rden <= fifo_rden;
  end

  always @(posedge clk) begin
    if (rst) begin
      wr_valid_reg <= 1'b0;
    end else if (fifo_rden && !fifo_is_empty) begin
      wr_valid_reg <= 1'b1;
    end else if ((wr_valid && wr_ready && !fifo_rden) || (fifo_rden && fifo_is_empty)) begin
      wr_valid_reg <= 1'b0;
    end else begin
      wr_valid_reg <= wr_valid_reg;
    end
  end

  always @(posedge clk) begin
    if (rst) begin
      wr_data_reg <= 32'h0;
    end else if (last_fifo_rden) begin
      wr_data_reg <= fifo_rdata;
    end else begin
      wr_data_reg <= wr_data_reg;  // retain previous value
    end
  end

  assign wr_req_addr = dest_base + tail_ptr + {wr_counter, 5'b0};
  assign wr_req_len = (wr_counter == total_burst_num - 1) ? last_burst_len : 5'd7;
  assign wr_req_valid = (current_state_WR == WR_REQ) && !fifo_is_empty && !wr_complete;
  assign wr_valid = wr_valid_reg && (current_state_WR == WR);
  assign wr_data = (last_fifo_rden) ? fifo_rdata : wr_data_reg;
  assign wr_last = (wr_last_counter == 0) && wr_valid && (current_state_WR == WR);

  assign fifo_rden = (wr_req_valid && wr_req_ready) || (current_state_WR == WR && (~wr_valid || wr_valid && wr_ready && !wr_last));
  assign fifo_wen = (current_state_RD == RD) && rd_valid && rd_ready;
  assign fifo_wdata = rd_rdata;


endmodule

