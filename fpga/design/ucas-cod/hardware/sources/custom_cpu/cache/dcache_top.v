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

// Masks for identifying special memory regions
`define NO_CACHE_MASK     32'hffffffe0 // Mask to identify non-cacheable memory regions
`define IO_SPACE_MASK     32'hc0000000 // Mask to identify I/O space regions

//==============================================================================
// Data Cache Top Module (dcache_top)
//==============================================================================
// This module implements a N-way set-associative data cache.
// It handles CPU memory read/write requests, supports write-back policy,
// and manages cache coherency (dirty bits) and bypass for non-cacheable regions.
//==============================================================================
module dcache_top (
    //--------------------------------------------------------------------------
    // Clock and Reset Signals
    //--------------------------------------------------------------------------
    input  clk,                            // System clock signal
    input  rst,                            // System reset signal (active high)

    //--------------------------------------------------------------------------
    // CPU Interface (Data Memory Access Path)
    //--------------------------------------------------------------------------
    // Signals for CPU making a memory/IO access request to Cache
    input         from_cpu_mem_req_valid,    // Valid signal for CPU's memory access request
    input         from_cpu_mem_req,          // CPU memory access type: 0 for read, 1 for write
    input  [31:0] from_cpu_mem_req_addr,     // Address for CPU's memory access (4-byte alignment assumed for cacheable)
    input  [31:0] from_cpu_mem_req_wdata,    // 32-bit write data from CPU
    input  [ 3:0] from_cpu_mem_req_wstrb,    // 4-bit write strobe from CPU (byte enables)
    output        to_cpu_mem_req_ready,      // Acknowledgement from Cache: Cache is ready for a new CPU memory request

    // Signals for Cache responding to CPU (for read operations)
    output        to_cpu_cache_rsp_valid,  // Valid signal for Cache's response to CPU
    output [31:0] to_cpu_cache_rsp_data,   // 32-bit read data from Cache/Memory to CPU
    input         from_cpu_cache_rsp_ready,// Acknowledgement from CPU: CPU is ready to receive read data

    //--------------------------------------------------------------------------
    // Memory/IO Read Interface (Used for Cache Misses and Bypass Reads)
    //--------------------------------------------------------------------------
    // Signals for Cache sending a memory/IO read request
    output        to_mem_rd_req_valid,     // Valid signal for Cache's memory/IO read request
    output [31:0] to_mem_rd_req_addr,      // Address for Cache's memory/IO read request
                                           // (4-byte alignment for I/O; 32-byte for cache line fetch)
    output [ 7:0] to_mem_rd_req_len,       // Burst length for memory read
                                           // (0 for I/O read - 1 beat; 7 for cache miss - 8 beats)
    input         from_mem_rd_req_ready,   // Acknowledgement from Memory: Memory is ready for Cache's read request

    // Signals for Memory returning read data to Cache
    input         from_mem_rd_rsp_valid,   // Valid signal for one data beat from Memory
    input  [31:0] from_mem_rd_rsp_data,    // 32-bit data beat from Memory
    input         from_mem_rd_rsp_last,    // Signal from Memory: Indicates if current data beat is the last
    output        to_mem_rd_rsp_ready,     // Acknowledgement from Cache: Cache is ready for current data beat

    //--------------------------------------------------------------------------
    // Memory/IO Write Interface (Used for Write-Backs and Bypass Writes)
    //--------------------------------------------------------------------------
    // Signals for Cache sending a memory/IO write request
    output        to_mem_wr_req_valid,     // Valid signal for Cache's memory/IO write request
    output [31:0] to_mem_wr_req_addr,      // Address for Cache's memory/IO write request
                                           // (4-byte for I/O/cache write-through miss; 32-byte for write-back)
    output [ 7:0] to_mem_wr_req_len,       // Burst length for memory write
                                           // (0 for I/O/cache write-through miss - 1 beat; 7 for write-back - 8 beats)
    input         from_mem_wr_req_ready,   // Acknowledgement from Memory: Memory is ready for Cache's write request

    // Signals for Cache sending memory/IO write data
    output        to_mem_wr_data_valid,    // Valid signal for current write data beat from Cache
    output [31:0] to_mem_wr_data,          // Current 32-bit write data beat from Cache
    output [ 3:0] to_mem_wr_data_strb,     // Write strobe for current data beat
                                           // (4'b1111 for write-back; CPU's wstrb for I/O/cache write-through)
    output        to_mem_wr_data_last,     // Signal from Cache: Indicates if current data beat is the last
    input         from_mem_wr_data_ready   // Acknowledgement from Memory/IO: Ready for current data beat
);

  // TODO: Please add your D-Cache code here (Original placeholder comment)

  //============================================================================
  // Finite State Machine (FSM) Definitions
  //============================================================================
  // FSM State Encoding for D-Cache operations
  localparam INIT          = 13'b00000_0000_0001; // Initialization state
  localparam WAIT_CPU      = 13'b00000_0000_0010; // Waiting for CPU memory access request
  localparam MISS_DT       = 13'b00000_0000_0100; // Dirty miss: need to write-back victim line first
  localparam MISS_CL       = 13'b00000_0000_1000; // Clean miss: can directly request new line from memory
  localparam SYNC          = 13'b00000_0001_0000; // Synchronization: writing back a dirty cache line to memory
  localparam REFILL        = 13'b00000_0010_0000; // Refilling a cache line from memory
  localparam W_HIT         = 13'b00000_0100_0000; // Write hit: CPU writes to an existing valid cache line
  localparam R_HIT         = 13'b00000_1000_0000; // Read hit: CPU reads from an existing valid cache line
  localparam SEND_CPU_DATA = 13'b00001_0000_0000; // Sending read data from cache to CPU
  localparam W_BP          = 13'b00010_0000_0000; // Write bypass request: for non-cacheable/IO write
  localparam R_BP          = 13'b00100_0000_0000; // Read bypass request: for non-cacheable/IO read
  localparam WRW           = 13'b01000_0000_0000; // Write word (bypass): sending data for bypass write
  localparam RDW           = 13'b10000_0000_0000; // Read word (bypass): receiving data for bypass read

  // FSM state registers
  reg [12:0] current_state; // Holds the current state of the FSM
  reg [12:0] next_state;    // Holds the calculated next state for the FSM

  //----------------------------------------------------------------------------
  // Address Decoding Logic
  //----------------------------------------------------------------------------
  // Decodes the incoming CPU memory request address into tag, index, and offset fields.
  wire [     `TAG_LEN - 1:0] tag;     // Tag field extracted from the CPU address
  wire [ `INDEX_WIDTH - 1:0] index;   // Index field (selects the cache set)
  wire [`OFFSET_WIDTH - 1:0] offset;  // Offset field (selects the word/byte within a cache line)

  assign tag    = from_cpu_mem_req_addr[31:`OFFSET_WIDTH + `INDEX_WIDTH];
  assign index  = from_cpu_mem_req_addr[`OFFSET_WIDTH + `INDEX_WIDTH - 1:`OFFSET_WIDTH];
  assign offset = from_cpu_mem_req_addr[`OFFSET_WIDTH - 1:0];

  //----------------------------------------------------------------------------
  // Cache Storage Arrays and Associated Signals (Per Way)
  //----------------------------------------------------------------------------
  // --- Single-bit signals for each cache way ---
  wire way_valids        [`CACHE_WAY - 1:0]; // way_valids[i]: 1 if way 'i' in the selected set contains a valid cache line.
  wire way_dirty         [`CACHE_WAY - 1:0]; // way_dirty[i]: 1 if way 'i' is dirty (modified and not yet written back).
  wire way_wen           [`CACHE_WAY - 1:0]; // way_wen[i]: General write enable for way 'i' (tag, data, valid, dirty, lru).
  wire way_wen_at_hit    [`CACHE_WAY - 1:0]; // way_wen_at_hit[i]: Specific write enable for dirty/data array on a write hit.
  wire way_wen_at_refill [`CACHE_WAY - 1:0]; // way_wen_at_refill[i]: Specific write enable for way 'i' during a refill.
  wire way_hits          [`CACHE_WAY - 1:0]; // way_hits[i]: 1 if way 'i' has a tag match and its valid bit is set.

  // --- Multi-bit vector signals for each cache way ---
  wire [`TAG_LEN    - 1:0] way_tags     [`CACHE_WAY - 1:0]; // way_tags[i]: The tag stored in way 'i' of the selected set.
  wire [`LINE_LEN   - 1:0] way_rdata    [`CACHE_WAY - 1:0]; // way_rdata[i]: The full cache line data read from way 'i'.
  wire [`LINE_LEN   - 1:0] way_wdata    [`CACHE_WAY - 1:0]; // way_wdata[i]: The full cache line data to be written into way 'i'.
  wire [`TIME_WIDTH - 1:0] way_last_hit [`CACHE_WAY - 1:0]; // way_last_hit[i]: Timestamp for LRU for way 'i'.

  // --- Signals related to overall cache operation and LRU ---
  reg  [`TIME_WIDTH - 1:0] lru_timestamp_counter; // Counter to generate timestamps for the LRU replacement policy.
  wire [              2:0] hit_way_index;         // Index of the cache way that registered a hit.
  wire [              2:0] replaced_way;          // Index of the cache way selected for replacement.

  // Example comments for clarifying multi-dimensional array declarations if they were complex:
  // (These are correctly declared in the provided code as arrays of vectors)
  // Example: wire [3:0] signal_array [NUM_ELEMENTS-1:0]; // An array of NUM_ELEMENTS, each a 4-bit vector.

  //----------------------------------------------------------------------------
  // FSM Transition, Status, and Internal Helper Signals
  //----------------------------------------------------------------------------
  wire hit;     // Overall cache hit signal.
  wire miss;    // Overall cache miss signal.
  wire dirty;   // Indicates if the `replaced_way` is dirty.
  wire Bypass;  // Indicates if the current CPU memory access should bypass the cache.
  wire w_done;  // Memory write (burst) done signal.
  wire r_done;  // Memory read (burst) done signal.

  //----------------------------------------------------------------------------
  // Cache Memory Array Instantiation (Generated for each cache way)
  //----------------------------------------------------------------------------
  genvar i; // Loop variable for the generate block
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin : gen_dcache_ways // Named generate block for each way
      //--- Valid Bit Array for Way i ---
      custom_array #(
          .TARRAY_DATA_WIDTH(1)           // Data width is 1 bit for the valid flag.
      ) valid_array_inst (
          .clk   (clk),                   // System clock
          .waddr (index),                 // Write address (set index)
          .raddr (index),                 // Read address (set index)
          .wen   (way_wen[i]),            // Write enable for this way's valid bit
          .rst   (rst),                   // System reset
          .wdata (1'b1),                  // Data to write (set to valid on refill/hit)
                                          // Note: wdata is always 1'b1; actual invalidation would need rst or specific logic.
          .rdata (way_valids[i])          // Data read (current valid bit status)
      );

      //--- Dirty Bit Array for Way i ---
      custom_array #(
          .TARRAY_DATA_WIDTH(1)           // Data width is 1 bit for the dirty flag.
      ) dirty_array_inst (
          .clk   (clk),
          .waddr (index),
          .raddr (index),
          .wen   (way_wen[i]),            // Write enable for this way's dirty bit
          .rst   (rst),
          // Data to write: set dirty bit if this way is written to on a hit.
          // On refill, dirty bit is typically cleared (not explicitly shown here,
          // implies `way_wen_at_hit` is 0 during refill path of `way_wen`).
          .wdata (way_wen_at_hit[i]),
          .rdata (way_dirty[i])           // Data read (current dirty bit status)
      );

      //--- Tag Array for Way i ---
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
      custom_array #(
          .TARRAY_DATA_WIDTH(`LINE_LEN)   // Data width is `LINE_LEN` bits (full cache line).
      ) data_array_inst (
          .clk   (clk),
          .waddr (index),
          .raddr (index),
          .wen   (way_wen[i]),            // Write enable for this way's data line
          .rst   (rst),
          .wdata (way_wdata[i]),          // Data to write (the cache line data)
          .rdata (way_rdata[i])           // Data read (stored cache line)
      );

      //--- Last Hit Timestamp Array (for LRU) for Way i ---
      custom_array #(
          .TARRAY_DATA_WIDTH(`TIME_WIDTH) // Data width is `TIME_WIDTH` bits.
      ) last_hit_array_inst (
          .clk   (clk),
          .waddr (index),
          .raddr (index),
          // Write enable: update timestamp only on a hit in this specific way
          // AND when the FSM is in WAIT_CPU state (processing a CPU request).
          .wen   ((current_state == WAIT_CPU) && way_hits[i]),
          .rst   (rst),
          .wdata (lru_timestamp_counter), // Data to write (the current global LRU timestamp)
          .rdata (way_last_hit[i])        // Data read (stored timestamp for this way)
      );
    end
  endgenerate

  //----------------------------------------------------------------------------
  // Replacement Policy Logic Instantiation (Simple - Placeholder for LRU)
  //----------------------------------------------------------------------------
  // This module determines which cache way to replace on a cache miss.
  // `replacement_simple` always chooses way 0. For a real LRU, use `replacement`.
  replacement_simple lru_replacement_inst (
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
  // Increments on cache hits to provide fresh timestamps for LRU.
  always @(posedge clk) begin
    if (rst) begin
      lru_timestamp_counter <= `TIME_WIDTH'b0; // Reset timestamp on system reset.
    // Increment if: FSM is WAIT_CPU, CPU request is valid, it's a cache hit,
    // and counter hasn't overflowed (using a wide 32-bit max check).
    end else if ((current_state == WAIT_CPU) && from_cpu_mem_req_valid && hit && lru_timestamp_counter != 32'hffff_ffff) begin
      lru_timestamp_counter <= lru_timestamp_counter + 1;
    end
  end

  //----------------------------------------------------------------------------
  // Write Burst Counter (for SYNC and WRW states)
  //----------------------------------------------------------------------------
  // `write_counts` tracks the number of data beats written to memory during
  // a cache line write-back (SYNC) or a bypass write (WRW).
  reg [3:0] write_counts; // Counter for up to 16 beats (8 needed for LINE_LEN=256, DATA_WIDTH=32)
  always @(posedge clk) begin
    if (rst || (current_state == WAIT_CPU)) begin
      // Reset counter on system reset or when returning to WAIT_CPU state.
      write_counts <= 4'b0;
    // Increment if in WRW (bypass write) or SYNC (write-back) state
    // AND memory is ready to accept the current data beat.
    end else if (((current_state == WRW) || (current_state == SYNC)) && from_mem_wr_data_ready) begin
      write_counts <= write_counts + 1;
    end
  end

  //----------------------------------------------------------------------------
  // Write-Back Buffer Register (sync_reg)
  //----------------------------------------------------------------------------
  // `sync_reg` temporarily stores the cache line data that is being written back
  // to memory during the SYNC state. It acts as a shift register.
  reg [`LINE_LEN - 1:0] sync_reg;
  always @(posedge clk) begin
    if (rst) begin
      sync_reg <= `LINE_LEN'b0; // Clear on reset.
    // When transitioning from MISS_DT (dirty miss) to SYNC (write-back),
    // if memory is ready for the write request, load the victim cache line
    // (data from the `replaced_way`) into `sync_reg`.
    end else if ((current_state == MISS_DT) && from_mem_wr_req_ready) begin
      sync_reg <= way_rdata[replaced_way];
    // During SYNC state, if memory accepts a data beat, shift `sync_reg`
    // to prepare the next `DATA_WIDTH` chunk for sending.
    // The MSBs are filled with zeros as data is shifted out from the LSBs.
    end else if ((current_state == SYNC) && from_mem_wr_data_ready) begin
      sync_reg <= {`DATA_WIDTH'b0, sync_reg[`LINE_LEN - 1 : `DATA_WIDTH]};
    end
  end

  //----------------------------------------------------------------------------
  // Memory Write Done Signal (w_done)
  //----------------------------------------------------------------------------
  // `w_done` indicates completion of a memory write operation (burst or single).
  assign w_done = ((current_state == SYNC) && (write_counts == 4'b1000)) || // Write-back done (8 beats for a 256-bit line)
                  ((current_state == WRW)  && (write_counts == 4'b0001));   // Bypass write done (1 beat)

  //----------------------------------------------------------------------------
  // Write Strobe Mask Generation
  //----------------------------------------------------------------------------
  // `mask` expands the 4-bit CPU write strobe (`from_cpu_mem_req_wstrb`)
  // into a 32-bit mask for byte-level updates within a 32-bit word.
  wire [31:0] mask;
  assign mask = {{8{from_cpu_mem_req_wstrb[3]}},  // Byte 3 mask
                 {8{from_cpu_mem_req_wstrb[2]}},  // Byte 2 mask
                 {8{from_cpu_mem_req_wstrb[1]}},  // Byte 1 mask
                 {8{from_cpu_mem_req_wstrb[0]}}}; // Byte 0 mask

  //----------------------------------------------------------------------------
  // Way Hit, Write Enable, and Write Data Signal Assignments (Per Way)
  //----------------------------------------------------------------------------
  generate
    for (i = 0; i < `CACHE_WAY; i = i + 1) begin : gen_dcache_way_logic
      //--- Way Hit Detection for Way i ---
      assign way_hits[i] = way_valids[i] && (way_tags[i] == tag);

      //--- Write Enable for Way i on a Write Hit ---
      // Asserted if this way hits, CPU request is valid and is a write, and FSM is in W_HIT.
      assign way_wen_at_hit[i] = way_hits[i] && from_cpu_mem_req_valid && (current_state == W_HIT);

      //--- Write Enable for Way i during Refill ---
      // Asserted if this way is chosen for replacement, FSM is REFILL, and memory response is valid.
      assign way_wen_at_refill[i] = (replaced_way == i) && (current_state == REFILL) && (from_mem_rd_rsp_valid);

      //--- Overall Write Enable for Way i ---
      // Way 'i' is written to either on a write hit or during a refill.
      assign way_wen[i] = way_wen_at_hit[i] || way_wen_at_refill[i];

      //--- Write Data for Way i (`way_wdata[i]`) ---
      assign way_wdata[i] = (way_wen_at_hit[i]) ?
                            // On a write hit:
                            // Perform a masked write to the specific word within the cache line.
                            // 1. `(~({{(`LINE_LEN - `DATA_WIDTH){1'b0}}, mask} << {offset[`OFFSET_WIDTH - 1:2], 5'b0}) & way_rdata[i])`:
                            //    Clears the target word in the existing cache line data (`way_rdata[i]`) using the inverted shifted mask.
                            //    `{offset[`OFFSET_WIDTH-1:2], 5'b0}` calculates the bit offset of the target word.
                            // 2. `({{(`LINE_LEN - `DATA_WIDTH){1'b0}}, (from_cpu_mem_req_wdata & mask)} << {offset[`OFFSET_WIDTH - 1:2], 5'b0})`:
                            //    Takes the CPU's write data, applies the byte mask, and shifts it to the target word position.
                            // 3. The two results are ORed to merge the updated word with the rest of the cache line.
                            ( (~({{(`LINE_LEN - `DATA_WIDTH){1'b0}}, mask} << {offset[`OFFSET_WIDTH - 1:2], 5'b0}) & way_rdata[i]) |
                              ({{(`LINE_LEN - `DATA_WIDTH){1'b0}}, (from_cpu_mem_req_wdata & mask)} << {offset[`OFFSET_WIDTH - 1:2], 5'b0}) ) :
                            (way_wen_at_refill[i]) ?
                            // During refill:
                            // Update a part of the cache line with data from memory. This structure suggests
                            // a burst refill where `from_mem_rd_rsp_data` is one beat, and it's combined with
                            // existing content of `way_rdata[i]`. This is similar to I-Cache.
                            ({from_mem_rd_rsp_data, way_rdata[i][`LINE_LEN - 1 : `DATA_WIDTH]}) :
                            // Otherwise (no write hit, no refill write for this way):
                            256'b0; // Default to zeros if not actively writing.
    end
  endgenerate

  //----------------------------------------------------------------------------
  // Overall Cache Hit, Miss, Dirty, and Hit Way Index Logic
  //----------------------------------------------------------------------------
  assign hit = way_hits[0] || way_hits[1] || way_hits[2] || way_hits[3] ||
               way_hits[4] || way_hits[5]; // True if any way hits.

  assign hit_way_index = // Determines which way caused the hit (priority to lower index).
               (way_hits[0]) ? 3'h0 :
               (way_hits[1]) ? 3'h1 :
               (way_hits[2]) ? 3'h2 :
               (way_hits[3]) ? 3'h3 :
               (way_hits[4]) ? 3'h4 :
               (way_hits[5]) ? 3'h5 :
                               3'b0; // Default to way 0.

  assign miss = from_cpu_mem_req_valid && !hit; // True if CPU request is valid and it's a miss.

  // `dirty` signal indicates if the cache line chosen for replacement (`replaced_way`) is dirty.
  // This is crucial for the write-back policy.
  assign dirty = way_dirty[replaced_way];


  //----------------------------------------------------------------------------
  // FSM State Register - Sequential Logic
  //----------------------------------------------------------------------------
  always @(posedge clk) begin
    if (rst) begin
      current_state <= INIT;     // Reset FSM to INIT state.
    end else begin
      current_state <= next_state; // Transition to the next calculated state.
    end
  end

  //----------------------------------------------------------------------------
  // Cache Bypass and Memory Read Completion Signals
  //----------------------------------------------------------------------------
  // `Bypass` is true if the CPU memory request address falls into a non-cacheable
  // region or I/O space, as defined by `NO_CACHE_MASK` and `IO_SPACE_MASK`.
  assign Bypass = (~|(from_cpu_mem_req_addr & `NO_CACHE_MASK)) || // Check against NO_CACHE_MASK
                  (|(from_cpu_mem_req_addr & `IO_SPACE_MASK));   // Check against IO_SPACE_MASK

  // `r_done` (read done) is asserted when memory signals a valid data beat
  // AND indicates it's the last beat of the burst.
  assign r_done = from_mem_rd_rsp_valid && from_mem_rd_rsp_last;

  //----------------------------------------------------------------------------
  // FSM Next State Determination - Combinational Logic
  //----------------------------------------------------------------------------
  always @(*) begin
    case (current_state)
      INIT: begin
        next_state = WAIT_CPU; // Initialize and go to wait for CPU.
      end

      WAIT_CPU: begin
        if (from_cpu_mem_req_valid) begin // If there's a valid CPU memory request:
          if (Bypass) begin
            // If address is in Bypass region:
            next_state = (from_cpu_mem_req) ? W_BP : R_BP; // Go to Write Bypass or Read Bypass.
          end else if (hit) begin
            // If cacheable and it's a cache hit:
            next_state = (from_cpu_mem_req) ? W_HIT : R_HIT; // Go to Write Hit or Read Hit.
          end else if (miss) begin
            // If cacheable and it's a cache miss:
            next_state = (dirty) ? MISS_DT : MISS_CL; // If victim is dirty, go to Dirty Miss (write-back), else Clean Miss.
          end else begin
            // Fallback, should ideally not be reached if logic is complete.
            next_state = WAIT_CPU;
          end
        end else begin
          // No valid CPU request, stay in WAIT_CPU.
          next_state = WAIT_CPU;
        end
      end

      W_HIT: begin // Write Hit state
        // After processing a write hit (data/dirty updated in arrays), return to wait for next CPU request.
        next_state = WAIT_CPU;
      end

      R_HIT: begin // Read Hit state
        // After a read hit is identified, transition to SEND_CPU_DATA to provide data to CPU.
        next_state = SEND_CPU_DATA;
      end

      SEND_CPU_DATA: begin // Sending data to CPU after a read hit
        // Wait for CPU to be ready to accept the data.
        next_state = (from_cpu_cache_rsp_ready) ? WAIT_CPU : SEND_CPU_DATA;
      end

      MISS_DT: begin // Dirty Miss state (need to write-back victim line)
        // Wait for memory to be ready to accept the write request for the write-back.
        next_state = (from_mem_wr_req_ready) ? SYNC : MISS_DT;
      end

      SYNC: begin // Synchronizing (writing back dirty line to memory)
        // If write-back is done (`w_done`), transition to MISS_CL to fetch the new line.
        // Otherwise, stay in SYNC to continue sending data.
        next_state = w_done ? MISS_CL : SYNC;
      end

      MISS_CL: begin // Clean Miss state (or after write-back from MISS_DT)
        // Wait for memory to be ready to accept the read request for the new line.
        next_state = (from_mem_rd_req_ready) ? REFILL : MISS_CL;
      end

      REFILL: begin // Refilling cache line from memory
        if (r_done) begin
          // If refill is complete, the original CPU request (that caused the miss) can now be served.
          // It should be a hit now. Go to W_HIT or R_HIT based on original request type.
          next_state = (from_cpu_mem_req) ? W_HIT : R_HIT;
        end else begin
          // If refill not done, continue refilling.
          next_state = REFILL;
        end
      end

      W_BP: begin // Write Bypass request state
        // Wait for memory to be ready for the bypass write data.
        next_state = (from_mem_wr_req_ready) ? WRW : W_BP;
      end

      R_BP: begin // Read Bypass request state
        // Wait for memory to be ready for the bypass read data.
        next_state = (from_mem_rd_req_ready) ? RDW : R_BP;
      end

      WRW: begin // Write Word (bypass) state
        // If bypass write is done (`w_done`), return to WAIT_CPU.
        // Otherwise, continue sending/waiting.
        next_state = (w_done) ? WAIT_CPU : WRW;
      end

      RDW: begin // Read Word (bypass) state
        // If bypass read is done (`r_done`), return to WAIT_CPU.
        // Otherwise, continue receiving/waiting.
        next_state = (r_done) ? WAIT_CPU : RDW;
      end

      default: begin
        // Default case for any undefined states, recover to WAIT_CPU.
        next_state = WAIT_CPU;
      end
    endcase
  end

  //----------------------------------------------------------------------------
  // CPU Interface - Handshake Signal Assignments
  //----------------------------------------------------------------------------
  // `to_cpu_mem_req_ready`: Signals to CPU that D-Cache is ready for a new memory request.
  // Cache is ready if:
  // - In WRW state and the bypass write is complete.
  // - In R_BP state (implying the read request to memory has been initiated or is about to be).
  // - In W_HIT state (write hit processed, ready for next).
  // - In R_HIT state (read hit identified, moving to SEND_CPU_DATA, effectively ready for next logical request).
  // Original comment: "// assign to_cpu_mem_req_ready = (current_state == WAIT_CPU); // naive logic, can be optimized"
  // The condition "could this be W_BP?" suggests W_BP might also be a ready state, but current logic is specific.
  assign to_cpu_mem_req_ready = ((current_state == WRW) && w_done) ||
                                (current_state == R_BP) ||
                                (current_state == W_HIT) ||
                                (current_state == R_HIT);

  // `to_cpu_cache_rsp_valid`: Signals valid read data to CPU.
  // Asserted if:
  // - In SEND_CPU_DATA state (sending data from a cache read hit).
  // - In RDW state (bypass read) AND the read from memory is complete (`r_done`).
  assign to_cpu_cache_rsp_valid = (current_state == SEND_CPU_DATA) || ((current_state == RDW) && r_done);

  // `to_cpu_cache_rsp_data`: The 32-bit data provided to the CPU.
  assign to_cpu_cache_rsp_data = (current_state == RDW) ?
                                 // If in RDW (bypass read), data comes directly from memory response.
                                 from_mem_rd_rsp_data :
                                 (current_state == SEND_CPU_DATA) ?
                                 // If in SEND_CPU_DATA (cache read hit), select word from hit cache line.
                                 // Logic for word selection within the line is similar to I-Cache.
                                 way_rdata[hit_way_index][{offset[`OFFSET_WIDTH - 1 : 2], 5'b0} +: `DATA_WIDTH] :
                                 // Otherwise, output zeros. `to_cpu_cache_rsp_valid` gates data consumption.
                                 32'b0;

  //----------------------------------------------------------------------------
  // Memory/IO Read Interface - Request and Response Signal Assignments
  //----------------------------------------------------------------------------
  // `to_mem_rd_req_valid`: Cache initiates a read from memory/IO.
  // Asserted if in MISS_CL (cache miss, need to fetch line) OR R_BP (read bypass).
  assign to_mem_rd_req_valid = (current_state == MISS_CL) || (current_state == R_BP);

  // `to_mem_rd_rsp_ready`: Cache is ready to receive data from memory/IO.
  // Asserted if in REFILL, RDW (bypass read), or INIT (potentially for memory init).
  assign to_mem_rd_rsp_ready = (current_state == REFILL) || (current_state == RDW) || (current_state == INIT);

  // `to_mem_rd_req_addr`: Address for the memory/IO read request.
  assign to_mem_rd_req_addr = (current_state == R_BP)    ?
                              // If Read Bypass, use the CPU's original request address.
                              from_cpu_mem_req_addr :
                              (current_state == MISS_CL) ?
                              // If Cache Miss (Clean), calculate line-aligned address.
                              {from_cpu_mem_req_addr[31:`OFFSET_WIDTH], 5'b0} :
                              // Default to zeros.
                              32'b0;

  // `to_mem_rd_req_len`: Burst length for memory read.
  assign to_mem_rd_req_len = (current_state == R_BP)    ?
                             // If Read Bypass, length is 0 (single beat).
                             8'd0 :
                             (current_state == MISS_CL) ?
                             // If Cache Miss, length is 7 (request 8 beats for a full cache line).
                             8'd7 :
                             // Default to 0.
                             8'd0;

  //----------------------------------------------------------------------------
  // Memory/IO Write Interface - Request and Data Signal Assignments
  //----------------------------------------------------------------------------
  // `to_mem_wr_req_valid`: Cache initiates a write to memory/IO.
  // Asserted if in MISS_DT (dirty miss, need write-back) OR W_BP (write bypass).
  assign to_mem_wr_req_valid = (current_state == MISS_DT) || (current_state == W_BP);

  // `to_mem_wr_req_addr`: Address for the memory/IO write request.
  assign to_mem_wr_req_addr = (current_state == W_BP) ?
                              // If Write Bypass, use the CPU's original request address.
                              from_cpu_mem_req_addr :
                              (current_state == MISS_DT) ?
                              // If Dirty Miss (write-back), construct address from victim line's tag and current index.
                              // Forms the base address of the dirty line being written back.
                              {way_tags[replaced_way], index, 5'b0} :
                              // Default to zeros.
                              32'b0;

  // `to_mem_wr_req_len`: Burst length for memory write.
  assign to_mem_wr_req_len = (current_state == W_BP)    ?
                             // If Write Bypass, length is 0 (single beat).
                             8'd0 :
                             (current_state == MISS_DT) ?
                             // If Dirty Miss (write-back), length is 7 (write 8 beats for a full cache line).
                             8'd7 :
                             // Default to 0.
                             8'd0;

  // `to_mem_wr_data`: Data beat to be written to memory/IO.
  assign to_mem_wr_data = (current_state == WRW) ?
                          // If in WRW (bypass write), data is directly from CPU.
                          from_cpu_mem_req_wdata :
                          (current_state == SYNC) ?
                          // If in SYNC (write-back), data is the current LSB word of `sync_reg`.
                          sync_reg[`DATA_WIDTH - 1:0] :
                          // Default to zeros.
                          32'b0;

  // `to_mem_wr_data_strb`: Write strobe for the memory/IO write data.
  assign to_mem_wr_data_strb = (current_state == WRW) ?
                               // If in WRW (bypass write), use CPU's original strobe.
                               from_cpu_mem_req_wstrb :
                               (current_state == SYNC) ?
                               // If in SYNC (write-back), all bytes are valid (full word write).
                               4'b1111 :
                               // Default to no strobes.
                               4'b0;

  // `to_mem_wr_data_valid`: Signals that `to_mem_wr_data` is valid.
  // Asserted if in WRW (sending bypass write data) OR SYNC (sending write-back data).
  assign to_mem_wr_data_valid = (current_state == WRW) || (current_state == SYNC);

  // `to_mem_wr_data_last`: Signals if the current write data beat is the last in the burst.
  assign to_mem_wr_data_last = ((current_state == WRW) && (write_counts == 4'b0000)) || // For WRW, last after 0th beat is sent (implies write_counts increments from 0 to 1 for the single beat)
                               ((current_state == SYNC) && (write_counts == 4'b0111)); // For SYNC, last when 7th beat (index 7) is being sent (write_counts will be 7, about to become 8)

endmodule // End of module dcache_top

//==============================================================================
// LRU Replacement Policy Module (replacement)
//==============================================================================
// Implements a true LRU policy for a 6-way cache by comparing timestamps.
// If all timestamps are maxed out (indicating all ways were recently hit
// and the timestamp counter wrapped), it falls back to a pseudo-random
// (round-robin in this case) replacement.
//==============================================================================
`define MAX_32_BIT 32'hffff_ffff // Define for maximum timestamp value comparison (used in 'full' logic)
                                  // Note: If TIME_WIDTH is small (e.g., 4), this MAX_32_BIT comparison
                                  // against TIME_WIDTH-bit inputs is effectively always false unless inputs are also 32-bit.
                                  // Assuming data_X inputs are `TIME_WIDTH` wide, `full` would check if they are `MAX_32_BIT` truncated to `TIME_WIDTH`.

module replacement (
    input                        clk,                // System clock
    input                        rst,                // System reset
    input  [`TIME_WIDTH - 1 : 0] data_0,             // Timestamp for way 0
    input  [`TIME_WIDTH - 1 : 0] data_1,             // Timestamp for way 1
    input  [`TIME_WIDTH - 1 : 0] data_2,             // Timestamp for way 2
    input  [`TIME_WIDTH - 1 : 0] data_3,             // Timestamp for way 3
    input  [`TIME_WIDTH - 1 : 0] data_4,             // Timestamp for way 4
    input  [`TIME_WIDTH - 1 : 0] data_5,             // Timestamp for way 5
    output [              2 : 0] replaced_way        // Output: Index of the way to be replaced (0-5)
);

    //--------------------------------------------------------------------------
    // Full Timestamp / Random Replacement Logic
    //--------------------------------------------------------------------------
    wire full;       // Signal to indicate if all way timestamps are at their maximum value.
    reg  [2 : 0] random_num; // Pseudo-random number generator (round-robin counter).

    // `full` is asserted if all input timestamps (`data_0` through `data_5`)
    // are equal to `MAX_32_BIT`.
    // Given `data_X` are `TIME_WIDTH` bits, this comparison's meaning depends
    // on how `MAX_32_BIT` is interpreted relative to `TIME_WIDTH`.
    // If `TIME_WIDTH` is 4, then `data_X` compared to `32'hffff_ffff` (truncated to 4 bits, i.e., `4'hf`)
    // means `full` is true if all timestamps are `4'hf`.
    assign full = (data_0 == `MAX_32_BIT) && (data_1 == `MAX_32_BIT) &&
                  (data_2 == `MAX_32_BIT) && (data_3 == `MAX_32_BIT) &&
                  (data_4 == `MAX_32_BIT) && (data_5 == `MAX_32_BIT);

    // Simple round-robin counter for pseudo-random replacement when `full` is true.
    always @(posedge clk) begin
        if (rst) begin
            random_num <= 3'b0;      // Reset to 0.
        end else if (random_num == 3'h5) begin // If max way index (5 for 6 ways)
            random_num <= 3'h0;      // Wrap around to 0.
        end else begin
            random_num <= random_num + 1; // Increment.
        end
    end

    //--------------------------------------------------------------------------
    // Pairwise Timestamp Comparison Logic
    //--------------------------------------------------------------------------
    // `le_XY` is true if timestamp of way X is less than timestamp of way Y.
    // This forms the basis for finding the way with the minimum timestamp (LRU).
    wire le_01, le_02, le_03, le_04, le_05, // Comparisons involving way 0
         le_12, le_13, le_14, le_15,        // Comparisons involving way 1 (excluding way 0)
         le_23, le_24, le_25,               // Comparisons involving way 2 (excluding way 0, 1)
         le_34, le_35,                      // Comparisons involving way 3 (excluding way 0, 1, 2)
         le_45;                             // Comparison between way 4 and way 5

    // These registers store whether each way is the "least" (has the smallest timestamp).
    // Only one of these should ideally be true if timestamps are unique.
    reg  least_0, least_1, least_2,
         least_3, least_4, least_5;

    // Assign comparison results
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

    //--------------------------------------------------------------------------
    // Determine the Least Recently Used Way
    //--------------------------------------------------------------------------
    // Combinational logic to determine which `least_X` signal is true.
    // Example: `least_0` is true if `data_0` is less than all other `data_Y`.
    always @(posedge clk) begin // Note: This is sequential, but models combinational if inputs are stable.
                                // For true combinational, use `always @(*)` or continuous assignments.
                                // However, `least_X` are regs, so this is pipelined.
        least_0 <=  le_01 &&  le_02 &&  le_03 &&  le_04 &&  le_05;
        least_1 <= !le_01 &&  le_12 &&  le_13 &&  le_14 &&  le_15;
        least_2 <= !le_02 && !le_12 &&  le_23 &&  le_24 &&  le_25;
        least_3 <= !le_03 && !le_13 && !le_23 &&  le_34 &&  le_35;
        least_4 <= !le_04 && !le_14 && !le_24 && !le_34 &&  le_45;
        least_5 <= !le_05 && !le_15 && !le_25 && !le_35 && !le_45;
    end

    //--------------------------------------------------------------------------
    // Select Replaced Way Output
    //--------------------------------------------------------------------------
    // If `full` is true, use `random_num` to select the replaced way.
    // Otherwise, select the way corresponding to the asserted `least_X` signal.
    // This is a multiplexer based on `full` and the `least_X` signals.
    assign replaced_way = { // Bitwise OR of conditional selections. Only one condition (full or one least_X) should be true.
        ({3{ full           }} & random_num) | // If 'full', select random_num (replicated to 3 bits)
        ({3{!full && least_0}} &       3'h0) | // If not 'full' and way 0 is LRU, select way 0
        ({3{!full && least_1}} &       3'h1) | // If not 'full' and way 1 is LRU, select way 1
        ({3{!full && least_2}} &       3'h2) | // ... and so on
        ({3{!full && least_3}} &       3'h3) |
        ({3{!full && least_4}} &       3'h4) |
        ({3{!full && least_5}} &       3'h5)
    };

endmodule // End of module replacement

//==============================================================================
// Simplified Replacement Policy Module (replacement_simple)
//==============================================================================
// This module implements a very simple replacement policy: always choose way 0.
// Used as a placeholder or for basic testing before a full LRU is implemented.
//==============================================================================
module replacement_simple (
    input                        clk,                // System clock (unused in this simple version)
    input                        rst,                // System reset (unused)
    input  [`TIME_WIDTH - 1 : 0] data_0,             // Timestamp for way 0 (unused)
    input  [`TIME_WIDTH - 1 : 0] data_1,             // Timestamp for way 1 (unused)
    input  [`TIME_WIDTH - 1 : 0] data_2,             // Timestamp for way 2 (unused)
    input  [`TIME_WIDTH - 1 : 0] data_3,             // Timestamp for way 3 (unused)
    input  [`TIME_WIDTH - 1 : 0] data_4,             // Timestamp for way 4 (unused)
    input  [`TIME_WIDTH - 1 : 0] data_5,             // Timestamp for way 5 (unused)
    output [              2 : 0] replaced_way        // Output: Index of the way to be replaced
);

  // Always select way 0 for replacement.
  assign replaced_way = 3'h0;

endmodule // End of module replacement_simple
