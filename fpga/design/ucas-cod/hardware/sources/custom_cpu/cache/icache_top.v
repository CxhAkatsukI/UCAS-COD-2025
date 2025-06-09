`timescale 10ns / 1ns

`define CACHE_SET 8
`define CACHE_WAY 6
`define DATA_WIDTH 32
`define TIME_WIDTH 32
`define TAG_LEN 24
`define INDEX_WIDTH 3
`define LINE_LEN 256
`define OFFSET_WIDTH 5
`define NO_CACHE_MASK 32'hffffffe0
`define IO_SPACE_MASK 32'hc0000000

module icache_top (
    input clk,
    input rst,

    //CPU interface
    /** CPU instruction fetch request to Cache: valid signal */
    input         from_cpu_inst_req_valid,
    /** CPU instruction fetch request to Cache: address (4 byte alignment) */
    input  [31:0] from_cpu_inst_req_addr,
    /** Acknowledgement from Cache: ready to receive CPU instruction fetch request */
    output        to_cpu_inst_req_ready,

    /** Cache responses to CPU: valid signal */
    output        to_cpu_cache_rsp_valid,
    /** Cache responses to CPU: 32-bit Instruction value */
    output [31:0] to_cpu_cache_rsp_data,
    /** Acknowledgement from CPU: Ready to receive Instruction */
    input         from_cpu_cache_rsp_ready,

    //Memory interface (32 byte aligned address)
    /** Cache sending memory read request: valid signal */
    output        to_mem_rd_req_valid,
    /** Cache sending memory read request: address (32 byte alignment) */
    output [31:0] to_mem_rd_req_addr,
    /** Acknowledgement from memory: ready to receive memory read request */
    input         from_mem_rd_req_ready,

    /** Memory return read data: valid signal of one data beat */
    input         from_mem_rd_rsp_valid,
    /** Memory return read data: 32-bit one data beat */
    input  [31:0] from_mem_rd_rsp_data,
    /** Memory return read data: if current data beat is the last in this burst data transmission */
    input         from_mem_rd_rsp_last,
    /** Acknowledgement from cache: ready to receive current data beat */
    output        to_mem_rd_rsp_ready
);

  //TODO: Please add your I-Cache code here

  // FSM implementation
  localparam INIT = 13'b00000_0000_0001,
             WAIT_CPU = 13'b00000_0000_0010,
             MISS_DT = 13'b00000_0000_0100,
             MISS_CL = 13'b00000_0000_1000,
             SYNC = 13'b00000_0001_0000,
             REFILL = 13'b00000_0010_0000,
             W_HIT = 13'b00000_0100_0000,
             R_HIT = 13'b00000_1000_0000,
             SEND_CPU_DATA = 13'b00001_0000_0000,
             W_BP = 13'b00010_0000_0000,
             R_BP = 13'b00100_0000_0000,
             WRW = 13'b01000_0000_0000,
             RDW = 13'b10000_0000_0000;

  reg  [12:0] current_state;
  reg  [12:0] next_state;

  // decode the CPU request address
  wire [     `TAG_LEN - 1:0] tag;
  wire [ `INDEX_WIDTH - 1:0] index;
  wire [`OFFSET_WIDTH - 1:0] offset;

  assign tag    = from_cpu_inst_req_addr[31:`OFFSET_WIDTH + `INDEX_WIDTH];
  assign index  = from_cpu_inst_req_addr[`OFFSET_WIDTH + `INDEX_WIDTH - 1:`OFFSET_WIDTH];
  assign offset = from_cpu_inst_req_addr[`OFFSET_WIDTH - 1:0];

  // information from cache blocks (and related control/status signals)

  // Arrays of single-bit signals (for each way)
  wire way_valids        [`CACHE_WAY - 1:0]; // valid bits for each way (Correct as is)
  wire way_wen           [`CACHE_WAY - 1:0]; // write enable for each way (Correct as is)
  wire way_wen_at_refill [`CACHE_WAY - 1:0]; // write enable for refill (Correct as is)
  wire way_hits          [`CACHE_WAY - 1:0]; // hit signals for each way (Correct as is)

  // Arrays where each element is a multi-bit vector (for each way)
  // Syntax: wire [ELEMENT_WIDTH - 1:0] array_name [ARRAY_SIZE - 1:0];
  wire [`TAG_LEN    - 1:0] way_tags     [`CACHE_WAY - 1:0]; // tags for each way
  wire [`LINE_LEN   - 1:0] way_rdata    [`CACHE_WAY - 1:0]; // data read from each way
  wire [`LINE_LEN   - 1:0] way_wdata    [`CACHE_WAY - 1:0]; // data to be written to each way (calculated value)
  wire [`TIME_WIDTH - 1:0] way_last_hit [`CACHE_WAY - 1:0]; // last hit time for each way

  // Single multi-bit signals (vectors) or registers
  // These are NOT arrays of ways, but single values.
  reg  [`TIME_WIDTH - 1:0]  lru_timestamp_counter; // timestamp for LRU (should be reg as it's assigned in always@posedge)
  wire [2:0]                hit_way_index;       // index of the way that was hit (vector, not array)
  wire [2:0]                replaced_way;        // index of the way that was replaced (vector, not array)

  // define the wires that drive the FSM transitions
  wire hit, miss;
  wire r_done;

  // generate cache
  genvar i;
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin
      custom_array #(
        .TARRAY_DATA_WIDTH(1)
      ) valid_array (
        .clk(clk),
        .waddr(index),
        .raddr(index),
        .wen(way_wen[i]),
        .rst(rst),
        .wdata(1'b1), // write valid bit
        .rdata(way_valids[i])
      );

     custom_array #(
        .TARRAY_DATA_WIDTH(`TAG_LEN)
      ) tag_array (
        .clk(clk),
        .waddr(index),
        .raddr(index),
        .wen(way_wen[i]),
        .rst(rst),
        .wdata(tag), // write tag
        .rdata(way_tags[i])
      );

      custom_array #(
        .TARRAY_DATA_WIDTH(`LINE_LEN)
      ) data_array (
        .clk(clk),
        .waddr(index),
        .raddr(index),
        .wen(way_wen[i]),
        .rst(rst),
        .wdata(way_wdata[i]), // write data
        .rdata(way_rdata[i])
      );

      custom_array #(
        .TARRAY_DATA_WIDTH(`TIME_WIDTH)
      ) last_hit_array (
        .clk(clk),
        .waddr(index),
        .raddr(index),
        .wen(current_state == WAIT_CPU && way_hits[i]),
        .rst(rst),
        .wdata(lru_timestamp_counter), // write last hit time
        .rdata(way_last_hit[i])
      );
    end
  endgenerate

  replacement lru_replacement (
    .clk(clk),
    .rst(rst),
    .data_0(way_last_hit[0]),
    .data_1(way_last_hit[1]),
    .data_2(way_last_hit[2]),
    .data_3(way_last_hit[3]),
    .data_4(way_last_hit[4]),
    .data_5(way_last_hit[5]),
    .replaced_way(replaced_way)
  );

  // generate the lru_timestamp_counter
  always @(posedge clk) begin
    if (rst)
      lru_timestamp_counter <= `TIME_WIDTH'b0;
    else if (current_state == WAIT_CPU && from_cpu_inst_req_valid && hit && lru_timestamp_counter != 32'hffff_ffff)
      lru_timestamp_counter <= lru_timestamp_counter + 1;
  end

  // generate the hit, wen and wdata signals
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin
      assign way_hits[i] = way_valids[i] && (way_tags[i] == tag);
      assign way_wen_at_refill[i] = (replaced_way == i) && (current_state == REFILL) && (from_mem_rd_rsp_valid); // only enable write when mem rsp is valid!
      assign way_wen[i] = way_wen_at_refill[i]; // write enable for the way that was hit or refilled
      assign way_wdata[i] = (way_wen_at_refill[i]) ? ({from_mem_rd_rsp_data, way_rdata[i][`LINE_LEN - 1 : `DATA_WIDTH]}) :
                            256'b0;
    end
  endgenerate

  assign hit = way_hits[0] || way_hits[1] || way_hits[2] || way_hits[3] ||
               way_hits[4] || way_hits[5]; // hit if any way is valid and tag matches
  assign hit_way_index =
               (way_hits[0]) ? 3'h0 :
               (way_hits[1]) ? 3'h1 :
               (way_hits[2]) ? 3'h2 :
               (way_hits[3]) ? 3'h3 :
               (way_hits[4]) ? 3'h4 :
               (way_hits[5]) ? 3'h5 :
                               3'b0; // index of the way that was hit
  assign miss = from_cpu_inst_req_valid && !hit; // miss if request is valid and no hit

  always @(posedge clk) begin
    if (rst) begin
      current_state <= INIT;
    end else begin
      current_state <= next_state;
    end
  end

  assign r_done = from_mem_rd_rsp_valid && from_mem_rd_rsp_last; // Read done when memory response is valid and last beat

  always @(*) begin
    case (current_state)
      INIT: begin
        next_state = WAIT_CPU;  // Start in INIT state, then wait for CPU request
      end
      WAIT_CPU: begin
        if (from_cpu_inst_req_valid) begin
          if (hit) begin
            next_state = R_HIT;  // Write or Read hit
          end else if (miss) begin
            next_state = MISS_CL;  // Write miss or Read miss
          end else begin
            next_state = WAIT_CPU;  // If no conditions met, stay in WAIT_CPU (should not happen)
          end
        end else begin
          next_state = WAIT_CPU;
        end
      end
      R_HIT: begin
        next_state = SEND_CPU_DATA;  // After read hit, send data as well as handshake signals to CPU
      end
      SEND_CPU_DATA: begin
        next_state = (from_cpu_cache_rsp_ready) ? WAIT_CPU : SEND_CPU_DATA;  // Wait for CPU to be ready to receive data
      end
      MISS_CL: begin
        next_state = (from_mem_rd_req_ready) ? REFILL : MISS_CL;  // Wait for memory read request to be ready
      end
      REFILL: begin
        if (r_done) begin
          next_state = R_HIT;  // After refill, go to hit state
        end else begin
          next_state = REFILL;  // Continue refilling if not done
        end
      end
      default: begin
        next_state = WAIT_CPU;  // Default case to handle unexpected states
      end
    endcase
  end

  // handshake signals between cache and CPU
  // assign to_cpu_mem_req_ready = (current_state == WAIT_CPU); // naive logic,
  // can be optimized
  assign to_cpu_inst_req_ready = (current_state == R_HIT);

  assign to_cpu_cache_rsp_valid = (current_state == SEND_CPU_DATA);

  assign to_cpu_cache_rsp_data = (current_state == SEND_CPU_DATA) ? way_rdata[hit_way_index][{offset[`OFFSET_WIDTH - 1 : 2], 5'b0} +: `DATA_WIDTH] :
                                 32'b0; // Read data from memory or cache, follow the alignment rules

  // memory read/write interface
  assign to_mem_rd_req_valid = (current_state == MISS_CL);
  assign to_mem_rd_rsp_ready = (current_state == REFILL) || (current_state == INIT); // INIT is for the reset logic

  assign to_mem_rd_req_addr = (current_state == MISS_CL) ?
                              {from_cpu_inst_req_addr[`DATA_WIDTH - 1:`OFFSET_WIDTH], 5'b0} : 32'b0;

endmodule
