`timescale 10ns / 1ns

`define CACHE_SET 8
`define CACHE_WAY 6
`define DATA_WIDTH 32
`define TIME_WIDTH 16
`define TAG_LEN 24
`define INDEX_WIDTH 3
`define LINE_LEN 256
`define OFFSET_WIDTH 5
`define NO_CACHE_MASK 32'hffffffe0
`define IO_SPACE_MASK 32'hc0000000

module dcache_top (
    input clk,
    input rst,

    //CPU interface
    /** CPU memory/IO access request to Cache: valid signal */
    input         from_cpu_mem_req_valid,
    /** CPU memory/IO access request to Cache: 0 for read; 1 for write (when req_valid is high) */
    input         from_cpu_mem_req,
    /** CPU memory/IO access request to Cache: address (4 byte alignment) */
    input  [31:0] from_cpu_mem_req_addr,
    /** CPU memory/IO access request to Cache: 32-bit write data */
    input  [31:0] from_cpu_mem_req_wdata,
    /** CPU memory/IO access request to Cache: 4-bit write strobe */
    input  [ 3:0] from_cpu_mem_req_wstrb,
    /** Acknowledgement from Cache: ready to receive CPU memory access request */
    output        to_cpu_mem_req_ready,

    /** Cache responses to CPU: valid signal */
    output        to_cpu_cache_rsp_valid,
    /** Cache responses to CPU: 32-bit read data */
    output [31:0] to_cpu_cache_rsp_data,
    /** Acknowledgement from CPU: Ready to receive read data */
    input         from_cpu_cache_rsp_ready,

    //Memory/IO read interface
    /** Cache sending memory/IO read request: valid signal */
    output        to_mem_rd_req_valid,
    /** Cache sending memory read request: address
	  * 4 byte alignment for I/O read
	  * 32 byte alignment for cache read miss */
    output [31:0] to_mem_rd_req_addr,
    /** Cache sending memory read request: burst length
	  * 0 for I/O read (read only one data beat)
	  * 7 for cache read miss (read eight data beats) */
    output [ 7:0] to_mem_rd_req_len,
    /** Acknowledgement from memory: ready to receive memory read request */
    input         from_mem_rd_req_ready,

    /** Memory return read data: valid signal of one data beat */
    input         from_mem_rd_rsp_valid,
    /** Memory return read data: 32-bit one data beat */
    input  [31:0] from_mem_rd_rsp_data,
    /** Memory return read data: if current data beat is the last in this burst data transmission */
    input         from_mem_rd_rsp_last,
    /** Acknowledgement from cache: ready to receive current data beat */
    output        to_mem_rd_rsp_ready,

    //Memory/IO write interface
    /** Cache sending memory/IO write request: valid signal */
    output        to_mem_wr_req_valid,
    /** Cache sending memory write request: address
	  * 4 byte alignment for I/O write 
	  * 4 byte alignment for cache write miss
          * 32 byte alignment for cache write-back */
    output [31:0] to_mem_wr_req_addr,
    /** Cache sending memory write request: burst length
          * 0 for I/O write (write only one data beat)
          * 0 for cache write miss (write only one data beat)
          * 7 for cache write-back (write eight data beats) */
    output [ 7:0] to_mem_wr_req_len,
    /** Acknowledgement from memory: ready to receive memory write request */
    input         from_mem_wr_req_ready,

    /** Cache sending memory/IO write data: valid signal for current data beat */
    output        to_mem_wr_data_valid,
    /** Cache sending memory/IO write data: current data beat */
    output [31:0] to_mem_wr_data,
    /** Cache sending memory/IO write data: write strobe
	  * 4'b1111 for cache write-back 
	  * other values for I/O write and cache write miss according to the original CPU request*/
    output [ 3:0] to_mem_wr_data_strb,
    /** Cache sending memory/IO write data: if current data beat is the last in this burst data transmission */
    output        to_mem_wr_data_last,
    /** Acknowledgement from memory/IO: ready to receive current data beat */
    input         from_mem_wr_data_ready
);

  //TODO: Please add your D-Cache code here

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

  assign tag    = from_cpu_mem_req_addr[31:`OFFSET_WIDTH + `INDEX_WIDTH];
  assign index  = from_cpu_mem_req_addr[`OFFSET_WIDTH + `INDEX_WIDTH - 1:`OFFSET_WIDTH];
  assign offset = from_cpu_mem_req_addr[`OFFSET_WIDTH - 1:0];

  // information from cache blocks (and related control/status signals)

  // Arrays of single-bit signals (for each way)
  wire way_valids        [`CACHE_WAY - 1:0]; // valid bits for each way (Correct as is)
  wire way_dirty         [`CACHE_WAY - 1:0]; // dirty bits for each way (Correct as is)
  wire way_wen           [`CACHE_WAY - 1:0]; // write enable for each way (Correct as is)
  wire way_wen_at_hit    [`CACHE_WAY - 1:0]; // write enable for hit (Correct as is)
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

  // Other internal signals that were previously problematic if declared as multi-dimensional arrays incorrectly
  // (Ensure these are declared correctly where they are defined/assigned)
  // Example: if write_counts was wire write_counts [3:0], it should be reg [3:0] write_counts;
  // Example: if sync_reg was wire sync_reg [LINE_LEN-1:0], it should be reg [LINE_LEN-1:0] sync_reg;

  // define the wires that drive the FSM transitions
  wire hit, miss, dirty, Bypass;
  wire w_done, r_done;


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
        .TARRAY_DATA_WIDTH(1)
      ) dirty_array (
        .clk(clk),
        .waddr(index),
        .raddr(index),
        .wen(way_wen[i]),
        .rst(rst),
        .wdata(way_wen_at_hit[i]), // write dirty bit
        .rdata(way_dirty[i])
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
        .wen((current_state == WAIT_CPU) && way_hits[i]),
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
    else if ((current_state == WAIT_CPU) && from_cpu_mem_req_valid && hit && lru_timestamp_counter != 32'hffff_ffff)
      lru_timestamp_counter <= lru_timestamp_counter + 1;
  end

  // add a counter that counts the number of writes in states that need to
  // write to memory
  reg [3:0] write_counts;
  always @(posedge clk) begin
    if (rst || (current_state == WAIT_CPU))
      write_counts <= 4'b0;
    else if (((current_state == WRW) || (current_state == SYNC)) && from_mem_wr_data_ready)
      write_counts <= write_counts + 1;
  end

  reg [`LINE_LEN - 1:0] sync_reg;
  always @(posedge clk) begin
    if (rst)
      sync_reg <= `LINE_LEN'b0;
    else if ((current_state == MISS_DT) && from_mem_wr_req_ready)
      sync_reg <= way_rdata[replaced_way];
    else if ((current_state == SYNC) && from_mem_wr_data_ready)
      sync_reg <= {`DATA_WIDTH'b0, sync_reg[`LINE_LEN - 1 : `DATA_WIDTH]};
  end

  assign w_done = ((current_state == SYNC) && (write_counts == 4'b1000)) || ((current_state == WRW) && (write_counts == 4'b0001)); // Write done when all 8 beats are written

  wire [31:0] mask;
  assign mask = {{8{from_cpu_mem_req_wstrb[3]}},
                 {8{from_cpu_mem_req_wstrb[2]}},
                 {8{from_cpu_mem_req_wstrb[1]}},
                 {8{from_cpu_mem_req_wstrb[0]}}};

  // generate the hit, wen and wdata signals
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin
      assign way_hits[i] = way_valids[i] && (way_tags[i] == tag);
      assign way_wen_at_hit[i] = way_hits[i] && from_cpu_mem_req_valid && (current_state == W_HIT);
      assign way_wen_at_refill[i] = (replaced_way == i) && (current_state == REFILL) && (from_mem_rd_rsp_valid); // only enable write when mem rsp is valid!
      assign way_wen[i] = way_wen_at_hit[i] || way_wen_at_refill[i]; // write enable for the way that was hit or refilled
      assign way_wdata[i] = (way_wen_at_hit[i]) ? (
                            (~({{(`LINE_LEN - `DATA_WIDTH){1'b0}}, mask} << {offset[`OFFSET_WIDTH - 1:2], 5'b0}) & way_rdata[i]) | ({{(`LINE_LEN - `DATA_WIDTH){1'b0}}, (from_cpu_mem_req_wdata & mask)} << {offset[`OFFSET_WIDTH - 1:2], 5'b0})
                            ) :
                            (way_wen_at_refill[i]) ? ({from_mem_rd_rsp_data, way_rdata[i][`LINE_LEN - 1 : `DATA_WIDTH]}) :
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
  assign miss = from_cpu_mem_req_valid && !hit; // miss if request is valid and no hit
  assign dirty = way_dirty[replaced_way]; // dirty if the way that was hit is dirty


  always @(posedge clk) begin
    if (rst) begin
      current_state <= INIT;
    end else begin
      current_state <= next_state;
    end
  end


  assign Bypass = (~|(from_cpu_mem_req_addr & `NO_CACHE_MASK)) || (|(from_cpu_mem_req_addr & `IO_SPACE_MASK)); // Bypass if address is in I/O space
  assign r_done = from_mem_rd_rsp_valid && from_mem_rd_rsp_last; // Read done when memory response is valid and last beat

  always @(*) begin
    case (current_state)
      INIT: begin
        next_state = WAIT_CPU;  // Start in INIT state, then wait for CPU request
      end
      WAIT_CPU: begin
        if (from_cpu_mem_req_valid) begin
          if (Bypass) begin
            next_state = (from_cpu_mem_req) ? W_BP : R_BP;  // Bypass logic for write or read
          end else if (hit) begin
            next_state = (from_cpu_mem_req) ? W_HIT : R_HIT;  // Write or Read hit
          end else if (miss) begin
            next_state = (dirty) ? MISS_DT : MISS_CL;  // Write miss or Read miss
          end else begin
            next_state = WAIT_CPU;  // If no conditions met, stay in WAIT_CPU (should not happen)
          end
        end else begin
          next_state = WAIT_CPU;
        end
      end
      W_HIT: begin
        next_state = WAIT_CPU;
      end
      R_HIT: begin
        next_state = SEND_CPU_DATA;  // After read hit, send data as well as handshake signals to CPU
      end
      SEND_CPU_DATA: begin
        next_state = (from_cpu_cache_rsp_ready) ? WAIT_CPU : SEND_CPU_DATA;  // Wait for CPU to be ready to receive data
      end
      MISS_DT: begin
        next_state = (from_mem_wr_req_ready) ? SYNC : MISS_DT;  // Wait for memory write request to be ready
      end
      SYNC: begin
        next_state = w_done ? MISS_CL : SYNC;  // Wait for write to complete
      end
      MISS_CL: begin
        next_state = (from_mem_rd_req_ready) ? REFILL : MISS_CL;  // Wait for memory read request to be ready
      end
      REFILL: begin
        if (r_done) begin
          next_state = (from_cpu_mem_req) ? W_HIT : R_HIT;  // After refill, go to hit state
        end else begin
          next_state = REFILL;  // Continue refilling if not done
        end
      end
      W_BP: begin
        next_state = (from_mem_wr_req_ready) ? WRW : W_BP;  // Bypass write, wait
      end
      R_BP: begin
        next_state = (from_mem_rd_req_ready) ? RDW : R_BP;  // Bypass read, wait
      end
      WRW: begin
        next_state = (w_done) ? WAIT_CPU : WRW;  // Wait for write to complete
      end
      RDW: begin
        next_state = (r_done) ? WAIT_CPU : RDW;  // Wait for read to complete
      end
      default: begin
        next_state = WAIT_CPU;  // Default case to handle unexpected states
      end
    endcase
  end

  // handshake signals between cache and CPU
  // assign to_cpu_mem_req_ready = (current_state == WAIT_CPU); // naive logic,
  // can be optimized
  assign to_cpu_mem_req_ready = ((current_state == WRW) && w_done) ||  // could this be W_BP?
      (current_state == R_BP) || (current_state == W_HIT) || (current_state == R_HIT);

  assign to_cpu_cache_rsp_valid = (current_state == SEND_CPU_DATA) || ((current_state == RDW) && r_done);

  assign to_cpu_cache_rsp_data = (current_state == RDW) ? from_mem_rd_rsp_data :
                                 (current_state == SEND_CPU_DATA) ? way_rdata[hit_way_index][{offset[`OFFSET_WIDTH - 1 : 2], 5'b0} +: `DATA_WIDTH] :
                                 32'b0; // Read data from memory or cache, follow the alignment rules

  // memory read/write interface
  assign to_mem_rd_req_valid = (current_state == MISS_CL) || (current_state == R_BP);
  assign to_mem_rd_rsp_ready = (current_state == REFILL) || (current_state == RDW) || (current_state == INIT); // INIT is for the reset logic

  assign to_mem_rd_req_addr = (current_state == R_BP)    ? from_cpu_mem_req_addr :
                              (current_state == MISS_CL) ?
                              {from_cpu_mem_req_addr[`DATA_WIDTH - 1:`OFFSET_WIDTH], 5'b0} : 32'b0;
  assign to_mem_rd_req_len = (current_state == R_BP)    ? 8'd0 :
                             (current_state == MISS_CL) ? 8'd7 :
                                                          8'd0; // 0 for I/O read, 7 for cache read miss

  assign to_mem_wr_req_valid = (current_state == MISS_DT) || (current_state == W_BP);
  assign to_mem_wr_req_addr = (current_state == W_BP) ? from_cpu_mem_req_addr :
                              (current_state == MISS_DT) ?
                              {way_tags[replaced_way], index, 5'b0} : 32'b0;
  assign to_mem_wr_req_len = (current_state == W_BP)    ? 8'd0 :
                             (current_state == MISS_DT) ? 8'd7 :
                                                          8'd0; // 0 for I/O write, 7 for cache write-back
  assign to_mem_wr_data = (current_state == WRW) ? from_cpu_mem_req_wdata :
                          (current_state == SYNC) ? sync_reg[`DATA_WIDTH - 1:0] : 32'b0;
  assign to_mem_wr_data_strb = (current_state == WRW) ? from_cpu_mem_req_wstrb :
                               (current_state == SYNC) ? 4'b1111 : 4'b0; // 4'b1111 for cache write-back
  assign to_mem_wr_data_valid = (current_state == WRW) || (current_state == SYNC);
  assign to_mem_wr_data_last = ((current_state == WRW) && (write_counts == 4'b0000)) || 
                               ((current_state == SYNC) && (write_counts == 4'b0111)); // Last beat for write

endmodule

`define MAX_32_BIT 32'hffff_ffff
module replacement (
    input                        clk,
    input                        rst,
    input  [`TIME_WIDTH - 1 : 0] data_0, data_1, data_2,
                                 data_3, data_4, data_5,
    output [              2 : 0] replaced_way
);


    wire         full;
    reg  [2 : 0] random_num;

    assign full = (data_0 == `MAX_32_BIT) && (data_1 == `MAX_32_BIT) &&
                  (data_2 == `MAX_32_BIT) && (data_3 == `MAX_32_BIT) &&
                  (data_4 == `MAX_32_BIT) && (data_5 == `MAX_32_BIT);

    always @(posedge clk) begin
        if (rst)
            random_num <= 3'b0;
        else if (random_num == 3'h5)
            random_num <= 3'h0;
        else
            random_num <= random_num + 1;
    end

    wire le_01, le_02, le_03, le_04, le_05,
         le_12, le_13, le_14, le_15, le_23,
         le_24, le_25, le_34, le_35, le_45;

    reg  least_0, least_1, least_2,
         least_3, least_4, least_5;

    assign le_01 = (data_0 < data_1);
    assign le_02 = (data_0 < data_2);
    assign le_03 = (data_0 < data_3);
    assign le_04 = (data_0 < data_4);
    assign le_05 = (data_0 < data_5);
    assign le_12 = (data_1 < data_2);
    assign le_13 = (data_1 < data_3);
    assign le_14 = (data_1 < data_4);
    assign le_15 = (data_1 < data_5);
    assign le_23 = (data_2 < data_3);
    assign le_24 = (data_2 < data_4);
    assign le_25 = (data_2 < data_5);
    assign le_34 = (data_3 < data_4);
    assign le_35 = (data_3 < data_5);
    assign le_45 = (data_4 < data_5);


    always @(posedge clk) begin
        least_0 <=  le_01 &&  le_02 &&  le_03 &&  le_04 &&  le_05;
        least_1 <= !le_01 &&  le_12 &&  le_13 &&  le_14 &&  le_15;
        least_2 <= !le_02 && !le_12 &&  le_23 &&  le_24 &&  le_25;
        least_3 <= !le_03 && !le_13 && !le_23 &&  le_34 &&  le_35;
        least_4 <= !le_04 && !le_14 && !le_24 && !le_34 &&  le_45;
        least_5 <= !le_05 && !le_15 && !le_25 && !le_35 && !le_45;
    end


    assign replaced_way = {
        ({3{ full           }} & random_num) |
        ({3{!full && least_0}} &       3'h0) |
        ({3{!full && least_1}} &       3'h1) |
        ({3{!full && least_2}} &       3'h2) |
        ({3{!full && least_3}} &       3'h3) |
        ({3{!full && least_4}} &       3'h4) |
        ({3{!full && least_5}} &       3'h5)
    };

endmodule

module replacement_simple (
    input                        clk,
    input                        rst,
    input  [`TIME_WIDTH - 1 : 0] data_0, data_1, data_2,
                                 data_3, data_4, data_5,
    output [              2 : 0] replaced_way
);

assign replaced_way = 0;
endmodule