// Timescale directive for simulation: 10ns simulation unit, 1ns precision
`timescale 10ns / 1ns

//==============================================================================
// Cache Configuration Parameters
//==============================================================================
`define CACHE_SET         8   // Number of sets in the cache (determines number of index bits)
`define CACHE_WAY         6   // Associativity of the cache (number of ways per set)
`define DATA_WIDTH        32  // Width of data bus in bits (e.g., CPU word size)
`define TIME_WIDTH        4   // Width of the LRU timestamp in bits
`define TAG_LEN           24  // Length of the tag field in an address
`define INDEX_WIDTH       3   // Width of the index field in an address (2^INDEX_WIDTH = CACHE_SET)
`define LINE_LEN          256 // Length of a cache line in bits (e.g., 32 bytes)
`define OFFSET_WIDTH      5   // Width of the offset field in an address (2^OFFSET_WIDTH = LINE_LEN/8 bytes)

// Masks for identifying special memory regions (Note: These are general defines,
// NO_CACHE_MASK and IO_SPACE_MASK are typically more relevant for D-Cache or unified caches)
`define NO_CACHE_MASK     32'hffffffe0 // Example mask for non-cacheable regions
`define IO_SPACE_MASK     32'hc0000000 // Example mask for I/O space

//==============================================================================
// Instruction Cache Top Module (icache_top)
//==============================================================================
// This module implements a N-way set-associative instruction cache.
// It handles instruction fetch requests from the CPU and interfaces with
// main memory to service cache misses.
//==============================================================================
module icache_top (
    //--------------------------------------------------------------------------
    // Clock and Reset Signals
    //--------------------------------------------------------------------------
    input  clk,                            // System clock signal
    input  rst,                            // System reset signal (active high)

    //--------------------------------------------------------------------------
    // CPU Interface (Instruction Fetch Path)
    //--------------------------------------------------------------------------
    // Signals for CPU requesting an instruction from Cache
    input         from_cpu_inst_req_valid,   // Valid signal for CPU's instruction fetch request
    input  [31:0] from_cpu_inst_req_addr,    // Address for the CPU's instruction fetch request (4-byte alignment assumed)
    output        to_cpu_inst_req_ready,   // Acknowledgement from Cache: Cache is ready to receive a new CPU request

    // Signals for Cache responding to CPU with an instruction
    output        to_cpu_cache_rsp_valid,  // Valid signal for Cache's response to CPU
    output [31:0] to_cpu_cache_rsp_data,   // 32-bit instruction data from Cache to CPU
    input         from_cpu_cache_rsp_ready,// Acknowledgement from CPU: CPU is ready to receive the instruction

    //--------------------------------------------------------------------------
    // Memory Interface (Used for Cache Miss Handling - 32 byte aligned address)
    //--------------------------------------------------------------------------
    // Signals for Cache sending a memory read request
    output        to_mem_rd_req_valid,     // Valid signal for Cache's memory read request
    output [31:0] to_mem_rd_req_addr,      // Address for Cache's memory read request (32-byte alignment for cache line fetch)
    input         from_mem_rd_req_ready,   // Acknowledgement from Memory: Memory is ready to receive Cache's read request

    // Signals for Memory returning read data to Cache
    input         from_mem_rd_rsp_valid,   // Valid signal for one data beat returned by Memory
    input  [31:0] from_mem_rd_rsp_data,    // 32-bit data beat returned by Memory
    input         from_mem_rd_rsp_last,    // Signal from Memory: Indicates if current data beat is the last in this burst
    output        to_mem_rd_rsp_ready      // Acknowledgement from Cache: Cache is ready to receive current data beat
);

  // TODO: Please add your I-Cache code here (Original placeholder comment)

  //============================================================================
  // Finite State Machine (FSM) Definitions
  //============================================================================
  // FSM State Encoding. Many states are placeholders or more typical for a D-Cache.
  localparam INIT          = 13'b00000_0000_0001; // Initialization state
  localparam WAIT_CPU      = 13'b00000_0000_0010; // Waiting for CPU instruction request
  localparam MISS_DT       = 13'b00000_0000_0100; // State for dirty miss (D-Cache specific, not used in I-Cache)
  localparam MISS_CL       = 13'b00000_0000_1000; // State for clean miss / I-Cache miss: request line from memory
  localparam SYNC          = 13'b00000_0001_0000; // State for synchronization/write-back (D-Cache specific)
  localparam REFILL        = 13'b00000_0010_0000; // State for refilling cache line from memory
  localparam W_HIT         = 13'b00000_0100_0000; // State for write hit (D-Cache specific)
  localparam LOOKUP        = 13'b00000_1000_0000; // State for cache lookup (functionality often part of WAIT_CPU)
  localparam SEND_CPU_DATA = 13'b00001_0000_0000; // State for sending data to CPU (functionality often part of WAIT_CPU on hit)
  localparam W_BP          = 13'b00010_0000_0000; // State for write bypass (D-Cache specific)
  localparam R_BP          = 13'b00100_0000_0000; // State for read bypass (D-Cache specific)
  localparam WRW           = 13'b01000_0000_0000; // State for write word bypass (D-Cache specific)
  localparam RDW           = 13'b10000_0000_0000; // State for read word bypass (D-Cache specific)

  // FSM state registers
  reg [12:0] current_state; // Holds the current state of the FSM
  reg [12:0] next_state;    // Holds the calculated next state for the FSM

  //----------------------------------------------------------------------------
  // Address Decoding Logic
  //----------------------------------------------------------------------------
  // Decodes the incoming CPU instruction request address into tag, index, and offset fields.
  wire [     `TAG_LEN - 1:0] tag;     // Tag field extracted from the CPU address
  wire [ `INDEX_WIDTH - 1:0] index;   // Index field (selects the cache set)
  wire [`OFFSET_WIDTH - 1:0] offset;  // Offset field (selects the word/byte within a cache line)

  assign tag    = from_cpu_inst_req_addr[31:`OFFSET_WIDTH + `INDEX_WIDTH];
  assign index  = from_cpu_inst_req_addr[`OFFSET_WIDTH + `INDEX_WIDTH - 1:`OFFSET_WIDTH];
  assign offset = from_cpu_inst_req_addr[`OFFSET_WIDTH - 1:0];

  //----------------------------------------------------------------------------
  // Cache Storage Arrays and Associated Signals (Per Way)
  //----------------------------------------------------------------------------
  // These signals represent the outputs from and inputs to the cache memory arrays.

  // --- Single-bit signals for each cache way ---
  wire way_valids[`CACHE_WAY - 1:0];         // way_valids[i]: 1 if way 'i' in the selected set contains a valid cache line.
  wire way_wen[`CACHE_WAY - 1:0];            // way_wen[i]: Write enable for way 'i'. Asserted to write to tag, data, or valid arrays for this way.
  wire way_wen_at_refill[`CACHE_WAY - 1:0];  // way_wen_at_refill[i]: Specific write enable for way 'i' during a refill operation.
  wire way_hits[`CACHE_WAY - 1:0];           // way_hits[i]: 1 if way 'i' has a tag match and its valid bit is set.

  // --- Multi-bit vector signals for each cache way ---
  wire [`TAG_LEN    - 1:0] way_tags[`CACHE_WAY - 1:0];     // way_tags[i]: The tag stored in way 'i' of the selected set.
  wire [`LINE_LEN   - 1:0] way_rdata[`CACHE_WAY - 1:0];    // way_rdata[i]: The full cache line data read from way 'i'.
  wire [`LINE_LEN   - 1:0] way_wdata[`CACHE_WAY - 1:0];    // way_wdata[i]: The full cache line data to be written into way 'i'.
  wire [`TIME_WIDTH - 1:0] way_last_hit[`CACHE_WAY - 1:0]; // way_last_hit[i]: Timestamp of the last hit for way 'i', used by LRU.

  // --- Signals related to overall cache operation and LRU ---
  reg  [`TIME_WIDTH - 1:0] lru_timestamp_counter; // Counter to generate timestamps for the LRU replacement policy.
  wire [              2:0] hit_way_index;         // Index of the cache way that registered a hit.
  wire [              2:0] replaced_way;          // Index of the cache way selected by LRU for replacement on a miss.

  //----------------------------------------------------------------------------
  // FSM Transition and Status Signals
  //----------------------------------------------------------------------------
  wire hit;   // Overall cache hit signal (logical OR of all way_hits).
  wire miss;  // Overall cache miss signal (valid CPU request and no hit).
  wire r_done; // Memory read done signal (indicates end of memory burst transfer).

  //----------------------------------------------------------------------------
  // Cache Memory Array Instantiation (Generated for each cache way)
  //----------------------------------------------------------------------------
  genvar i; // Loop variable for the generate block
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin : gen_cache_ways // Named generate block for each way
      //--- Valid Bit Array for Way i ---
      // Stores the valid status of the cache line in this way.
      custom_array #(
          .TARRAY_DATA_WIDTH(1)           // Data width is 1 bit for the valid flag.
      ) valid_array_inst (
          .clk   (clk),                   // System clock
          .waddr (index),                 // Write address (set index)
          .raddr (index),                 // Read address (set index)
          .wen   (way_wen[i]),            // Write enable for this way's valid bit
          .rst   (rst),                   // System reset
          .wdata (1'b1),                  // Data to write (set to valid)
          .rdata (way_valids[i])          // Data read (current valid bit status)
      );

      //--- Tag Array for Way i ---
      // Stores the tag associated with the cache line in this way.
      custom_array #(
          .TARRAY_DATA_WIDTH(`TAG_LEN)    // Data width is `TAG_LEN` bits.
      ) tag_array_inst (
          .clk   (clk),
          .waddr (index),
          .raddr (index),
          .wen   (way_wen[i]),            // Write enable for this way's tag
          .rst   (rst),
          .wdata (tag),                   // Data to write (the tag from the current CPU address)
          .rdata (way_tags[i])            // Data read (stored tag)
      );

      //--- Data Array (Cache Line Storage) for Way i ---
      // Stores the actual instruction data for the cache line in this way.
      custom_array #(
          .TARRAY_DATA_WIDTH(`LINE_LEN)   // Data width is `LINE_LEN` bits (full cache line).
      ) data_array_inst (
          .clk   (clk),
          .waddr (index),
          .raddr (index),
          .wen   (way_wen[i]),            // Write enable for this way's data line
          .rst   (rst),
          .wdata (way_wdata[i]),          // Data to write (the cache line data, see way_wdata assignment)
          .rdata (way_rdata[i])           // Data read (stored cache line)
      );

      //--- Last Hit Timestamp Array (for LRU) for Way i ---
      // Stores the timestamp of the last access to this cache line, for LRU policy.
      custom_array #(
          .TARRAY_DATA_WIDTH(`TIME_WIDTH) // Data width is `TIME_WIDTH` bits.
      ) last_hit_array_inst (
          .clk   (clk),
          .waddr (index),
          .raddr (index),
          // Write enable: update timestamp only on a hit in this specific way
          // AND when the FSM is in WAIT_CPU state (i.e., processing a CPU request).
          .wen   (current_state == WAIT_CPU && way_hits[i]),
          .rst   (rst),
          .wdata (lru_timestamp_counter), // Data to write (the current global LRU timestamp)
          .rdata (way_last_hit[i])        // Data read (stored timestamp for this way)
      );
    end
  endgenerate

  //----------------------------------------------------------------------------
  // Replacement Policy Logic Instantiation (LRU)
  //----------------------------------------------------------------------------
  // This module determines which cache way to replace on a cache miss,
  // based on the LRU (Least Recently Used) algorithm using timestamps.
  replacement lru_replacement_inst (
      .clk          (clk),                // System clock
      .rst          (rst),                // System reset
      .data_0       (way_last_hit[0]),    // Timestamp of way 0
      .data_1       (way_last_hit[1]),    // Timestamp of way 1
      .data_2       (way_last_hit[2]),    // Timestamp of way 2
      .data_3       (way_last_hit[3]),    // Timestamp of way 3
      .data_4       (way_last_hit[4]),    // Timestamp of way 4
      .data_5       (way_last_hit[5]),    // Timestamp of way 5
      .replaced_way (replaced_way)        // Output: Index of the way chosen for replacement
  );

  //----------------------------------------------------------------------------
  // LRU Timestamp Counter Logic
  //----------------------------------------------------------------------------
  // This counter increments on each CPU request that results in a cache hit.
  // The counter's value is used as the timestamp written to the hit way's
  // last_hit_array entry, facilitating the LRU replacement policy.
  always @(posedge clk) begin
    if (rst) begin
      lru_timestamp_counter <= `TIME_WIDTH'b0; // Reset the timestamp counter.
    // Increment counter if all conditions are met:
    // 1. FSM is in WAIT_CPU state (actively serving or ready for CPU requests).
    // 2. A valid instruction request is coming from the CPU.
    // 3. The request results in a cache hit.
    // 4. The timestamp counter has not reached its maximum value (32'hffff_ffff).
    //    Note: This max value comparison (32'hffff_ffff) is very large compared to `TIME_WIDTH` (4 bits).
    //    For TIME_WIDTH=4, a more typical check would be against 4'b1111 (or 15).
    //    The current comparison will effectively always be true if lru_timestamp_counter is `TIME_WIDTH` bits.
    end else if (current_state == WAIT_CPU && from_cpu_inst_req_valid && hit && lru_timestamp_counter != 32'hffff_ffff) begin
      lru_timestamp_counter <= lru_timestamp_counter + 1;
    end
  end

  //----------------------------------------------------------------------------
  // Way Hit, Write Enable, and Write Data Signal Assignments
  //----------------------------------------------------------------------------
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin : gen_way_internal_logic
      //--- Way Hit Detection for Way i ---
      // A specific way 'i' registers a hit if its valid bit is set AND its stored tag
      // matches the tag part of the current CPU request address.
      assign way_hits[i] = way_valids[i] && (way_tags[i] == tag);

      //--- Write Enable for Way i during Refill ---
      // This signal is asserted to enable writing to way 'i' specifically when it's being refilled.
      // Conditions:
      //   1. Way 'i' is the one selected for replacement (`replaced_way == i`).
      //   2. The FSM is in the REFILL state (`current_state == REFILL`).
      //   3. Valid data is currently being received from memory (`from_mem_rd_rsp_valid`).
      assign way_wen_at_refill[i] = (replaced_way == i) && (current_state == REFILL) && (from_mem_rd_rsp_valid);

      //--- Overall Write Enable for Way i ---
      // For this I-Cache design, writes to the cache arrays (valid, tag, data)
      // only occur during a refill operation.
      assign way_wen[i] = way_wen_at_refill[i];

      //--- Write Data for Way i ---
      // Determines the `LINE_LEN` data to be written to the data array of way 'i'.
      assign way_wdata[i] = (way_wen_at_refill[i]) ?
                            // If writing to this way due to a refill operation:
                            // The data written (`way_wdata[i]`) is constructed as follows:
                            // - The most significant `DATA_WIDTH` bits are sourced from `from_mem_rd_rsp_data` (current data beat from memory).
                            // - The remaining (`LINE_LEN - DATA_WIDTH`) less significant bits are sourced from `way_rdata[i]`
                            //   (the data read from this way's data array in the current cycle).
                            // This construction implies a specific mechanism for assembling the full cache line
                            // over multiple memory beats if the refill is a burst, or how the `data_array` module
                            // handles partial line updates. For instance, this could be updating the MSB part of the line.
                            ({from_mem_rd_rsp_data, way_rdata[i][`LINE_LEN - 1 : `DATA_WIDTH]}) :
                            // If not writing to this way for refill (i.e., `way_wen_at_refill[i]` is false):
                            // Provide all zeros as the write data. This is a safe default if `way_wen[i]`
                            // were to be asserted under other (currently undefined) conditions.
                            256'b0;
    end
  endgenerate

  //----------------------------------------------------------------------------
  // Overall Cache Hit, Miss, and Hit Way Index Logic
  //----------------------------------------------------------------------------
  // `hit` is true if any of the cache ways register a hit for the current request.
  assign hit = way_hits[0] || way_hits[1] || way_hits[2] || way_hits[3] ||
               way_hits[4] || way_hits[5];

  // `hit_way_index` identifies which way caused the hit.
  // This is implemented as a priority encoder: if multiple ways were to hit
  // (which is generally not expected in a correctly functioning cache with unique tags per set),
  // this logic would select the lowest-indexed way among them.
  assign hit_way_index =
               (way_hits[0]) ? 3'h0 : // If way 0 hits
               (way_hits[1]) ? 3'h1 : // Else if way 1 hits
               (way_hits[2]) ? 3'h2 : // Else if way 2 hits
               (way_hits[3]) ? 3'h3 : // Else if way 3 hits
               (way_hits[4]) ? 3'h4 : // Else if way 4 hits
               (way_hits[5]) ? 3'h5 : // Else if way 5 hits
                               3'b0;  // Default to way 0 (e.g., if way_hits[0] is true, or on a miss, this value is latched but not necessarily used meaningfully for data selection)

  // `miss` is true if there is a valid CPU instruction request AND it does not result in a cache hit.
  assign miss = from_cpu_inst_req_valid && !hit;

  //----------------------------------------------------------------------------
  // FSM State Register - Sequential Logic
  //----------------------------------------------------------------------------
  // This block updates the FSM's current state on each rising edge of the clock.
  always @(posedge clk) begin
    if (rst) begin
      current_state <= INIT;     // On reset, the FSM enters the INIT state.
    end else begin
      current_state <= next_state; // In normal operation, transition to the `next_state` determined by combinational logic.
    end
  end

  //----------------------------------------------------------------------------
  // Memory Read Completion Signal
  //----------------------------------------------------------------------------
  // `r_done` (read done) is asserted when the memory system signals that the current
  // read data beat (`from_mem_rd_rsp_valid`) is valid AND it is the last data beat
  // of the ongoing burst transfer (`from_mem_rd_rsp_last`).
  assign r_done = from_mem_rd_rsp_valid && from_mem_rd_rsp_last;

  //----------------------------------------------------------------------------
  // FSM Next State Determination - Combinational Logic
  //----------------------------------------------------------------------------
  // This block combinatorially calculates the `next_state` of the FSM based on the
  // `current_state` and various input signals from the CPU and Memory interfaces.
  always @(*) begin
    case (current_state)
      INIT: begin
        // From the INITialization state, always transition to WAIT_CPU.
        next_state = WAIT_CPU;
      end

      WAIT_CPU: begin
        // When in WAIT_CPU state:
        if (from_cpu_inst_req_valid && hit) begin
          // If a valid CPU instruction request arrives AND it's a cache hit:
          // Remain in WAIT_CPU. The cache will provide the instruction to the CPU
          // (combinational outputs `to_cpu_cache_rsp_valid` and `to_cpu_cache_rsp_data` are active).
          // Ready to accept another request in the next cycle if CPU is ready.
          next_state = WAIT_CPU;
        end else if (from_cpu_inst_req_valid && !hit) begin
          // If a valid CPU instruction request arrives BUT it's a cache miss:
          // Transition to MISS_CL to initiate fetching the required cache line from memory.
          next_state = MISS_CL;
        end else begin
          // If there's no valid CPU request, or other undefined conditions:
          // Remain in WAIT_CPU.
          next_state = WAIT_CPU;
        end
      end

      LOOKUP: begin // Note: The LOOKUP state's role might overlap with WAIT_CPU in this FSM.
                    // It appears to be another state where hit/miss decisions are made.
        if (!hit) begin
          // If the lookup (presumably initiated before entering/while in LOOKUP) results in a miss:
          next_state = MISS_CL;
        end else if (from_cpu_cache_rsp_ready) begin
          // If it was a hit AND the CPU is ready to accept the cache response data:
          // Transition back to WAIT_CPU, assuming data has been or is being sent.
          next_state = WAIT_CPU;
        end else begin
          // If it was a hit but CPU is not ready, or other conditions:
          // Remain in LOOKUP state.
          next_state = LOOKUP;
        end
      end

      MISS_CL: begin
        // When in MISS_CL state (a cache miss has occurred, and a clean line or I-Cache line needs fetching):
        // The cache has signaled a read request to memory (see `to_mem_rd_req_valid`).
        // Wait for the memory system to be ready to accept this read request.
        next_state = (from_mem_rd_req_ready) ? REFILL : MISS_CL;
        // If memory is ready (`from_mem_rd_req_ready` is high), transition to REFILL.
        // Otherwise, stay in MISS_CL, continuing to assert the memory read request.
      end

      REFILL: begin
        // When in REFILL state (actively receiving data from memory to fill a cache line):
        if (r_done) begin
          // If the memory read operation is complete (`r_done` is high - last data beat received):
          // The cache line is now filled. Transition back to WAIT_CPU.
          // The CPU request that originally caused the miss can now be re-evaluated (it should hit).
          next_state = WAIT_CPU;
        end else begin
          // If the memory read is not yet complete (more data beats are expected):
          // Remain in REFILL state to continue receiving data.
          // (`to_mem_rd_rsp_ready` should be asserted by the cache in this state).
          next_state = REFILL;
        end
      end

      default: begin
        // For any undefined or unexpected FSM states:
        // Transition to WAIT_CPU as a safe recovery measure.
        next_state = WAIT_CPU;
      end
    endcase
  end

  //----------------------------------------------------------------------------
  // CPU Interface - Handshake Signal Assignments
  //----------------------------------------------------------------------------
  // `to_cpu_inst_req_ready`: Signals to the CPU that the cache is ready to accept a new instruction fetch request.
  // The cache is considered ready when it's in the WAIT_CPU state.
  // Original comment: "// assign to_cpu_mem_req_ready = (current_state == WAIT_CPU); // naive logic, can be optimized"
  // The port name is to_cpu_inst_req_ready, matching the I-Cache context.
  assign to_cpu_inst_req_ready = (current_state == WAIT_CPU);

  // `to_cpu_cache_rsp_valid`: Signals to the CPU that the cache has valid instruction data to provide on `to_cpu_cache_rsp_data`.
  // This is asserted if:
  //   1. The cache is in the WAIT_CPU state.
  //   2. There is a valid instruction request from the CPU (`from_cpu_inst_req_valid`).
  //   3. The request resulted in a cache hit (`hit`).
  assign to_cpu_cache_rsp_valid = (current_state == WAIT_CPU) && from_cpu_inst_req_valid && hit;

  // `to_cpu_cache_rsp_data`: The 32-bit instruction data sent from the cache to the CPU.
  assign to_cpu_cache_rsp_data = (from_cpu_inst_req_valid && hit) ?
                                 // If there's a valid CPU request and it's a cache hit:
                                 // Select the data from the cache way that registered the hit (`hit_way_index`).
                                 // The expression `{offset[`OFFSET_WIDTH - 1 : 2], 5'b0}` calculates the bit-aligned
                                 // start address of the desired 32-bit word within the `LINE_LEN` cache line.
                                 // `offset[`OFFSET_WIDTH - 1 : 2]` provides the word index within the cache line.
                                 // Concatenating `5'b0` effectively multiplies this word index by 32 (2^5),
                                 // yielding the starting bit position for Verilog's part-select `+:` operator.
                                 way_rdata[hit_way_index][{offset[`OFFSET_WIDTH - 1 : 2], 5'b0} +: `DATA_WIDTH] :
                                 // Otherwise (e.g., on a miss, or if no valid request though `hit` might be coincidentally true from a previous cycle's inputs):
                                 // Output all zeros. The `to_cpu_cache_rsp_valid` signal ensures CPU only takes data when valid.
                                 32'b0;

  //----------------------------------------------------------------------------
  // Memory Interface - Read Request and Response Signal Assignments
  //----------------------------------------------------------------------------
  // `to_mem_rd_req_valid`: Signals to the memory system that the cache has a valid read request.
  // This is asserted when the cache FSM is in the MISS_CL state, indicating a need to fetch a line from memory.
  assign to_mem_rd_req_valid = (current_state == MISS_CL);

  // `to_mem_rd_rsp_ready`: Signals to the memory system that the cache is ready to receive a data beat of a read response.
  // Asserted when the cache is in the REFILL state (actively filling a line).
  // Also asserted in INIT state; this might be for a memory clearing operation on reset or some other
  // initialization protocol, though not explicitly detailed by other logic.
  assign to_mem_rd_rsp_ready = (current_state == REFILL) || (current_state == INIT);

  // `to_mem_rd_req_addr`: The address sent to the memory system for the cache's read request.
  assign to_mem_rd_req_addr = (current_state == MISS_CL) ?
                              // If in MISS_CL state (cache miss):
                              // Construct the line-aligned address to be fetched from memory.
                              // This is done by taking the upper bits of the CPU's request address (tag and index fields)
                              // and appending `OFFSET_WIDTH` zeros to form a base address for the cache line.
                              // `from_cpu_inst_req_addr[`DATA_WIDTH - 1:`OFFSET_WIDTH]` extracts bits [31:5] of the address.
                              // Concatenating `5'b0` makes the lower 5 bits zero, aligning to a 32-byte boundary.
                              {from_cpu_inst_req_addr[31:`OFFSET_WIDTH], 5'b0} :
                              // Otherwise (if not in MISS_CL state):
                              // Output all zeros. The `to_mem_rd_req_valid` signal ensures memory only acts on valid requests.
                              32'b0;

endmodule // End of module icache_top
