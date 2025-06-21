`timescale 1ns / 1ps

module engine_core #(
    parameter integer DATA_WIDTH = 32
) (
    //--------------------------------------------------------------------------
    // Global Signals
    //--------------------------------------------------------------------------
    input  clk,
    input  rst,

    //--------------------------------------------------------------------------
    // CPU Interface - Control/Status Registers (CSR)
    //--------------------------------------------------------------------------
    output [31:0] src_base,         // Output: Source base address for the transfer.
    output [31:0] dest_base,        // Output: Destination base address.
    output [31:0] tail_ptr,         // Output: Tail pointer, advanced by DMA hardware.
    output [31:0] head_ptr,         // Output: Head pointer, advanced by CPU.
    output [31:0] dma_size,         // Output: Size of each sub-buffer transfer.
    output [31:0] ctrl_stat,        // Output: Control and status register.
    input  [31:0] reg_wr_data,      // Input: Data written by CPU to a CSR.
    input  [ 5:0] reg_wr_en,        // Input: One-hot write enable for CSRs.
    output        intr,             // Output: Interrupt request signal to CPU.

    //--------------------------------------------------------------------------
    // Read Engine - Memory Interface (Request Channel)
    //--------------------------------------------------------------------------
    output [31:0] rd_req_addr,      // Output: Address for the memory read request.
    output [ 4:0] rd_req_len,       // Output: Length of the read burst.
    output        rd_req_valid,     // Output: Indicates a valid read request.
    input         rd_req_ready,     // Input:  Indicates memory is ready for a read request.

    //--------------------------------------------------------------------------
    // Read Engine - Memory Interface (Data Channel)
    //--------------------------------------------------------------------------
    input  [31:0] rd_rdata,         // Input:  Data read from memory.
    input         rd_last,          // Input:  Indicates the last data of a read burst.
    input         rd_valid,         // Input:  Indicates valid data on rd_rdata.
    output        rd_ready,         // Output: Indicates DMA is ready for read data.

    //--------------------------------------------------------------------------
    // Write Engine - Memory Interface (Request Channel)
    //--------------------------------------------------------------------------
    output [31:0] wr_req_addr,      // Output: Address for the memory write request.
    output [ 4:0] wr_req_len,       // Output: Length of the write burst.
    output        wr_req_valid,     // Output: Indicates a valid write request.
    input         wr_req_ready,     // Input:  Indicates memory is ready for a write request.

    //--------------------------------------------------------------------------
    // Write Engine - Memory Interface (Data Channel)
    //--------------------------------------------------------------------------
    output [31:0] wr_data,          // Output: Data to be written to memory.
    output        wr_valid,         // Output: Indicates valid data on wr_data.
    input         wr_ready,         // Input:  Indicates memory has accepted the write data.
    output        wr_last,          // Output: Indicates the last data of a write burst.

    //--------------------------------------------------------------------------
    // Internal FIFO Interface
    //--------------------------------------------------------------------------
    output        fifo_rden,        // Output: Read enable signal to the internal FIFO.
    output [31:0] fifo_wdata,       // Output: Data to be written to the internal FIFO.
    output        fifo_wen,         // Output: Write enable signal to the internal FIFO.
    input  [31:0] fifo_rdata,       // Input:  Data read from the internal FIFO.
    input         fifo_is_empty,    // Input:  Flag indicating the FIFO is empty.
    input         fifo_is_full      // Input:  Flag indicating the FIFO is full.
);

    //==========================================================================
    // SECTION: Internal Signals and State Definitions
    //==========================================================================

    // --- Control Signal Aliases ---
    // Provides convenient access to specific bits of the control/status register.
    wire        EN   = ctrl_stat[0];    // DMA Enable bit.
    assign      intr = ctrl_stat[31];   // Interrupt Status bit.

    // --- State Machine Registers ---
    // Registers to hold the current and next states for both Read and Write FSMs.
    reg [2:0] current_state_RD, next_state_RD;
    reg [2:0] current_state_WR, next_state_WR;

    // --- Task Completion Flags ---
    // Wires to indicate the completion of a full sub-buffer read or write task.
    wire rd_complete, wr_complete;

    // --- FSM State Encoding ---
    // Defines the states for the dual-FSM architecture.
    localparam IDLE   = 3'b000,         // Waiting for a new task.
               RD_REQ = 3'b001,         // Read FSM: Issuing a memory read request.
               RD     = 3'b010,         // Read FSM: Receiving data from memory.
               WR_REQ = 3'b011,         // Write FSM: Issuing a memory write request.
               WR     = 3'b100;         // Write FSM: Sending data to memory.

    //==========================================================================
    // SECTION: CPU-Controlled Register File
    //==========================================================================

    // --- CSR Implementation ---
    // These registers are configured by the CPU and control the DMA's behavior.
    reg [31:0] src_base_reg;
    reg [31:0] dest_base_reg;
    reg [31:0] tail_ptr_reg;
    reg [31:0] head_ptr_reg;
    reg [31:0] dma_size_reg;
    reg [31:0] ctrl_stat_reg;

    // --- CSR Update Logic ---
    // This block handles writes from the CPU and automatic updates by the DMA hardware.
    always @(posedge clk) begin
        if (rst) begin
            src_base_reg  <= 32'h0;
            dest_base_reg <= 32'h0;
            tail_ptr_reg  <= 32'h0;
            head_ptr_reg  <= 32'h0;
            dma_size_reg  <= 32'h0;
            ctrl_stat_reg <= 32'h1; // Enable DMA by default on reset.
        end else if (|reg_wr_en[5:0]) begin
            // Priority 1: CPU writes take precedence.
            if (reg_wr_en[0]) src_base_reg  <= reg_wr_data;
            if (reg_wr_en[1]) dest_base_reg <= reg_wr_data;
            if (reg_wr_en[2]) tail_ptr_reg  <= reg_wr_data; // CPU can set initial tail.
            if (reg_wr_en[3]) head_ptr_reg  <= reg_wr_data; // CPU signals new data.
            if (reg_wr_en[4]) dma_size_reg  <= reg_wr_data;
            if (reg_wr_en[5]) ctrl_stat_reg <= reg_wr_data; // CPU can clear interrupt.
        end else if ((current_state_WR == WR_REQ) && wr_complete) begin
            // Priority 2: DMA hardware automatically updates upon task completion.
            ctrl_stat_reg <= {1'b1, ctrl_stat_reg[30:0]}; // Set interrupt flag.
            tail_ptr_reg  <= tail_ptr_reg + dma_size_reg; // Advance tail pointer.
            src_base_reg  <= src_base_reg;
            dest_base_reg <= dest_base_reg;
            head_ptr_reg  <= head_ptr_reg;
            dma_size_reg  <= dma_size_reg;
        end else begin
            // Default: Retain all register values.
            ctrl_stat_reg <= ctrl_stat_reg;
            src_base_reg  <= src_base_reg;
            dest_base_reg <= dest_base_reg;
            tail_ptr_reg  <= tail_ptr_reg;
            head_ptr_reg  <= head_ptr_reg;
            dma_size_reg  <= dma_size_reg;
        end
    end

    // --- CSR Output Assignments ---
    assign src_base  = src_base_reg;
    assign dest_base = dest_base_reg;
    assign tail_ptr  = tail_ptr_reg;
    assign head_ptr  = head_ptr_reg;
    assign dma_size  = dma_size_reg;
    assign ctrl_stat = ctrl_stat_reg;

    //==========================================================================
    // SECTION: Finite State Machine (FSM) Implementation
    //==========================================================================

    // --- State Register Update Logic (Synchronous) ---
    // This block updates the current state of both FSMs on each clock edge.
    always @(posedge clk) begin
        if (rst) begin
            current_state_RD <= IDLE;
            current_state_WR <= IDLE;
        end else begin
            current_state_RD <= next_state_RD;
            current_state_WR <= next_state_WR;
        end
    end

    // --- Next State Logic (Combinational) ---
    // This block determines the next state for both FSMs based on the current
    // state and various input conditions.
    always @(*) begin
        // Default assignment to prevent latches and to handle hold-state conditions.
        next_state_RD = current_state_RD;
        next_state_WR = current_state_WR;

        // --- Read FSM Logic ---
        case (current_state_RD)
            IDLE: begin
                // Transition from IDLE to RD_REQ if a task is available and the
                // write FSM is also ready to start (a conservative dependency).
                if (EN && (tail_ptr != head_ptr) && (current_state_WR == IDLE)) begin
                    next_state_RD = RD_REQ;
                end else begin
                    next_state_RD = IDLE;
                end
            end
            RD_REQ: begin
                // Once a read request is accepted by memory, move to the RD state.
                // If the entire read task is complete, return to IDLE.
                if (rd_req_ready && rd_req_valid) begin
                    next_state_RD = RD;
                end else if (rd_complete) begin
                    next_state_RD = IDLE;
                end else begin
                    next_state_RD = RD_REQ;
                end
            end
            RD: begin
                // After receiving the last piece of data in a burst (and if FIFO
                // has space), issue the next read request.
                if (rd_valid && rd_last && !fifo_is_full) begin
                    next_state_RD = RD_REQ;
                end else begin
                    next_state_RD = RD;
                end
            end
            default: begin
                next_state_RD = IDLE; // Safe fallback to IDLE state.
            end
        endcase

        // --- Write FSM Logic ---
        case (current_state_WR)
            IDLE: begin
                // Symmetrical to the Read FSM, starts when a task is available.
                if (EN && (tail_ptr != head_ptr) && (current_state_RD == IDLE)) begin
                    next_state_WR = WR_REQ;
                end else begin
                    next_state_WR = IDLE;
                end
            end
            WR_REQ: begin
                // Once a write request is accepted, move to the WR state.
                // If the entire write task is complete, return to IDLE.
                if (wr_req_ready && wr_req_valid) begin
                    next_state_WR = WR;
                end else if (wr_complete) begin
                    next_state_WR = IDLE;
                end else begin
                    next_state_WR = WR_REQ;
                end
            end
            WR: begin
                // After sending the last piece of data in a burst, issue the next write request.
                if (wr_valid && wr_last) begin
                    next_state_WR = WR_REQ;
                end else begin
                    next_state_WR = WR;
                end
            end
            default: begin
                next_state_WR = IDLE; // Safe fallback to IDLE state.
            end
        endcase
    end

    //==========================================================================
    // SECTION: Burst and Task Progress Tracking
    //==========================================================================

    // --- Burst Counters ---
    // These counters track the number of bursts completed for read and write operations.
    reg [27:0] rd_counter;
    reg [27:0] wr_counter;

    // --- Start-of-Task Signal ---
    // A one-shot signal indicating that a new DMA transfer task should begin.
    wire start_new_task = (current_state_RD == IDLE) && (current_state_WR == IDLE) && EN && (head_ptr != tail_ptr);

    // --- Burst Counter Update Logic ---
    always @(posedge clk) begin
        if (rst) begin
            rd_counter <= 28'h0;
            wr_counter <= 28'h0;
        end else if (start_new_task) begin
            // Reset counters only at the very beginning of a new task.
            rd_counter <= 28'h0;
            wr_counter <= 28'h0;
        end else begin
            // Increment read counter upon successful completion of a read burst.
            if (current_state_RD == RD && rd_valid && rd_last && !fifo_is_full && rd_ready) begin
                rd_counter <= rd_counter + 1;
            end
            // Increment write counter upon successful completion of a write burst.
            if (current_state_WR == WR && wr_valid && wr_last && wr_ready) begin
                wr_counter <= wr_counter + 1;
            end
        end
    end

    // --- Write Burst Data Counter ---
    // A down-counter to track the remaining data words in the current write burst.
    reg [2:0] wr_last_counter;

    always @(posedge clk) begin
        if (rst) begin
            wr_last_counter <= 3'b0;
        end else if ((current_state_WR == WR_REQ) && wr_req_ready && wr_req_valid) begin
            // Load the counter when a new write burst starts.
            wr_last_counter <= wr_req_len;
        end else if (wr_valid && wr_ready) begin
            // Decrement after each successful data word transfer.
            wr_last_counter <= wr_last_counter - 1;
        end else begin
            wr_last_counter <= wr_last_counter;
        end
    end

    // --- Burst Calculation Logic ---
    // Determines the total number of bursts and the length of the final, potentially smaller, burst.
    wire [27:0] total_burst_num = dma_size[31:5] + (|dma_size[4:0]);
    wire [ 2:0] last_burst_len  = dma_size[4:2] - {2'b0, !(|dma_size[1:0])};

    // --- Task Completion Logic ---
    // These flags are asserted when the counters match the total required bursts.
    assign rd_complete = (rd_counter == total_burst_num) && (rd_counter != 0);
    assign wr_complete = (wr_counter == total_burst_num) && (wr_counter != 0);

    //==========================================================================
    // SECTION: Read Engine Output Logic
    //==========================================================================

    // Address for the next read burst, calculated from base, tail, and burst counter.
    assign rd_req_addr  = src_base + tail_ptr + {rd_counter, 5'b0};
    // Length of the read burst. Standard size is 32 bytes (len=7), except for the last burst.
    assign rd_req_len   = (rd_counter == total_burst_num - 1) ? last_burst_len : 5'd7;
    // A read request is valid if in the REQ state, FIFO is empty (performance bottleneck), and task not done.
    assign rd_req_valid = (current_state_RD == RD_REQ) && fifo_is_empty && !rd_complete;
    // Ready to accept read data if in the RD state and FIFO is not full.
    assign rd_ready     = (current_state_RD == RD) && !fifo_is_full;

    //==========================================================================
    // SECTION: Write Engine Output Logic & Skid Buffer
    //==========================================================================

    // --- Skid Buffer Helper Signals ---
    // These registers form a 1-deep skid buffer to handle memory stalls without
    // losing data from the FIFO, which is only valid for one cycle after a read.
    reg last_fifo_rden; // Stores the fifo_rden signal from the previous cycle.
    reg wr_valid_reg;   // The internal, registered version of wr_valid.
    reg [31:0] wr_data_reg;    // A register to hold the data word during a stall.

    // --- Skid Buffer Logic ---
    always @(posedge clk) begin
        last_fifo_rden <= fifo_rden;
    end

    always @(posedge clk) begin
        if (rst) begin
            wr_valid_reg <= 1'b0;
        end else if (fifo_rden && !fifo_is_empty) begin
            // Pre-emptively set valid if a new data word is being requested.
            wr_valid_reg <= 1'b1;
        end else if ((wr_valid && wr_ready && !fifo_rden) || (fifo_rden && fifo_is_empty)) begin
            // Clear valid after a successful transfer (if no new data is requested)
            // or if the requested read from FIFO was empty.
            wr_valid_reg <= 1'b0;
        end else begin
            wr_valid_reg <= wr_valid_reg;
        end
    end

    always @(posedge clk) begin
        if (rst) begin
            wr_data_reg <= 32'h0;
        end else if (last_fifo_rden) begin
            // Latch the data from the FIFO on the cycle it becomes valid.
            wr_data_reg <= fifo_rdata;
        end else begin
            wr_data_reg <= wr_data_reg;
        end
    end

    // --- Write Engine Output Assignments ---
    // Address for the next write burst.
    assign wr_req_addr  = dest_base + tail_ptr + {wr_counter, 5'b0};
    // Length of the write burst.
    assign wr_req_len   = (wr_counter == total_burst_num - 1) ? last_burst_len : 5'd7;
    // A write request is valid if in REQ state, FIFO has data, and task not done.
    assign wr_req_valid = (current_state_WR == WR_REQ) && !fifo_is_empty && !wr_complete;
    // The final wr_valid signal, active only in the WR state.
    assign wr_valid     = wr_valid_reg && (current_state_WR == WR);
    // Data multiplexer: Choose fresh data from FIFO if available, otherwise use stalled data from register.
    assign wr_data      = (last_fifo_rden) ? fifo_rdata : wr_data_reg;
    // Assert wr_last only on the final data word of a burst.
    assign wr_last      = (wr_last_counter == 0) && wr_valid && (current_state_WR == WR);

    //==========================================================================
    // SECTION: FIFO Control Logic
    //==========================================================================

    // When to read from the FIFO: either a new write burst is starting, or we are
    // in the middle of a write burst and need more data.
    assign fifo_rden = (wr_req_valid && wr_req_ready) || (current_state_WR == WR && (~wr_valid || wr_valid && wr_ready && !wr_last));
    // When to write to the FIFO: when a valid data word is successfully read from memory.
    assign fifo_wen   = (current_state_RD == RD) && rd_valid && rd_ready;
    // Data to be written to the FIFO is the data coming from memory.
    assign fifo_wdata = rd_rdata;

endmodule
