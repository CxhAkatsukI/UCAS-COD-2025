`timescale 10ns / 1ns

`timescale 10ns / 1ns

module custom_cpu (
    input clk,
    input rst,

    //Instruction request channel
    output [31:0] PC, // This will be driven by internal pc_reg
    output        Inst_Req_Valid, // Driven by IFU
    input         Inst_Req_Ready, // To IFU

    //Instruction response channel
    input  [31:0] Instruction,    // To IFU
    input         Inst_Valid,       // To IFU
    output        Inst_Ready,       // Driven by IFU

    //Memory request channel
    output [31:0] Address,        // Driven by MEMU (or logic based on MEMU output)
    output        MemWrite,       // Driven by MEMU FSM
    output [31:0] Write_data,     // Driven by MEMU
    output [ 3:0] Write_strb,     // Driven by MEMU
    output        MemRead,        // Driven by MEMU FSM
    input         Mem_Req_Ready,  // To MEMU

    //Memory data response channel
    input  [31:0] Read_data,      // To MEMU
    input         Read_data_Valid,  // To MEMU
    output        Read_data_Ready,// Driven by MEMU FSM

    input intr, // Interrupt signal (TODO: integrate interrupt handling)

    // Performance Counters
    output [31:0] cpu_perf_cnt_0,
    output [31:0] cpu_perf_cnt_1,
    output [31:0] cpu_perf_cnt_2,
    output [31:0] cpu_perf_cnt_3,
    output [31:0] cpu_perf_cnt_4,
    output [31:0] cpu_perf_cnt_5,
    output [31:0] cpu_perf_cnt_6,
    output [31:0] cpu_perf_cnt_7,
    output [31:0] cpu_perf_cnt_8,
    output [31:0] cpu_perf_cnt_9,
    output [31:0] cpu_perf_cnt_10,
    output [31:0] cpu_perf_cnt_11,
    output [31:0] cpu_perf_cnt_12,
    output [31:0] cpu_perf_cnt_13,
    output [31:0] cpu_perf_cnt_14,
    output [31:0] cpu_perf_cnt_15,

    output [69:0] inst_retire     // Driven by WBU
);

    //--------------------------------------------------------------------------
    // Internal Pipeline Control Signals
    //--------------------------------------------------------------------------
    wire pipeline_advance_enable; // Global signal to advance pipeline stages
    wire ld_use_hazard_stall;     // Stall signal due to load-use hazard
    wire if_stage_ready;          // IFU is ready to pass instruction to ID
    wire mem_stage_ready;         // MEMU is ready to pass result to WB / handle next

    //--------------------------------------------------------------------------
    // PC Logic - PC IS NOW MANAGED ENTIRELY WITHIN IFU
    // We still need the next_pc calculated by IDU to feed into IFU.
    //--------------------------------------------------------------------------
    wire [31:0] next_pc_from_idu_internal; // Output from IDU, input to IFU

    //--------------------------------------------------------------------------
    // IF/ID Pipeline Register (FD - Fetch/Decode)
    //--------------------------------------------------------------------------
    reg [31:0] fd_instruction_reg;
    reg [31:0] fd_pc_reg;           // This PC is the PC of the instruction *in* this register
    reg        fd_inst_valid_reg;

    wire [31:0] ifu_IR_to_fd_reg;
    wire        ifu_valid_to_fd_reg;
    wire [31:0] pc_value_at_fetch_time; // Wire to capture PC from IFU for FD reg

    always @(posedge clk) begin
        if (rst) begin
            fd_instruction_reg <= 32'h00000013; // NOP
            fd_pc_reg          <= 32'h0;
            fd_inst_valid_reg  <= 1'b0;
          end else if (pipeline_advance_enable) begin
            if (ld_use_hazard_stall) begin
                // fd_instruction_reg <= 32'h00000013; // This signal eats the
                // instruction
                // fd_pc_reg remains or set to a NOP PC
                fd_inst_valid_reg  <= 1'b0;
              end else if (!if_stage_ready && pipeline_advance_enable) begin
                fd_inst_valid_reg  <= 1'b0;
              end else begin
                fd_instruction_reg <= ifu_IR_to_fd_reg;
                fd_pc_reg          <= pc_value_at_fetch_time; // PC of the fetched instruction
                fd_inst_valid_reg  <= ifu_valid_to_fd_reg;
            end
        end  else if (!ld_use_hazard_stall) begin
            fd_inst_valid_reg <= ifu_valid_to_fd_reg;
            end
    end

    //--------------------------------------------------------------------------
    // ID Stage Wires (Outputs from IDU)
    //--------------------------------------------------------------------------
    wire [2:0]  idu_alu_op_out;
    wire [31:0] idu_alu_src1_out;
    wire [31:0] idu_alu_src2_out;
    wire [1:0]  idu_shifter_op_out;
    wire [31:0] idu_shifter_src1_out;
    wire [31:0] idu_shifter_src2_out;
    wire        idu_is_alu_op_out;
    wire        idu_is_shifter_op_out;
    wire        idu_mem_read_out;
    wire        idu_mem_write_out;
    wire [2:0]  idu_mem_width_out;
    wire        idu_mem_signed_out;
    wire [31:0] idu_store_data_value_out; // Was 'write_data' from IDU
    wire        idu_rf_wen_out;
    wire [4:0]  idu_rf_waddr_out;         // This is 'rd' field for destination
    // wire [31:0] next_pc_from_idu_internal; // Already declared for PC logic
    wire [4:0]  idu_regfile_raddr1_out;   // To RegFile
    wire [4:0]  idu_regfile_raddr2_out;   // To RegFile
    wire [4:0]  idu_rs1_for_hazard_out;   // To FWDU/CU
    wire [4:0]  idu_rs2_for_hazard_out;   // To FWDU/CU
    wire        idu_branch_condition_out; // For Perf

    // Wires for data from Register File / Forwarding Unit (Inputs to IDU)
    wire [31:0] rf_read_data1_raw_internal;
    wire [31:0] rf_read_data2_raw_internal;
    wire [31:0] idu_final_operand1_in; // Operand1 after forwarding, to IDU
    wire [31:0] idu_final_operand2_in; // Operand2 after forwarding, to IDU

    //--------------------------------------------------------------------------
    // Register File
    //--------------------------------------------------------------------------
    wire        wb_rf_wen_internal;   // Write enable from MEM/WB stage
    wire [4:0]  wb_rf_waddr_internal; // Write address from MEM/WB stage
    wire [31:0] wb_rf_wdata_internal; // Data to write from MEM/WB stage

    reg_file reg_file_inst (
        .clk    (clk),
        .wen    (wb_rf_wen_internal),
        .waddr  (wb_rf_waddr_internal),
        .wdata  (wb_rf_wdata_internal),
        .raddr1 (idu_regfile_raddr1_out), // From IDU
        .raddr2 (idu_regfile_raddr2_out), // From IDU
        .rdata1 (rf_read_data1_raw_internal), // To FWDU
        .rdata2 (rf_read_data2_raw_internal)  // To FWDU
    );

    //--------------------------------------------------------------------------
    // ID/EX Pipeline Register (Internal: de_..._reg)
    //--------------------------------------------------------------------------
    reg [31:0] de_pc_reg;
    reg        de_inst_valid_reg;
    reg [31:0] de_alu_src1_reg;       // Was idu_alu_src1_out
    reg [31:0] de_alu_src2_reg;       // Was idu_alu_src2_out
    reg [2:0]  de_alu_op_reg;         // Was idu_alu_op_out
    reg [31:0] de_shifter_src1_reg;
    reg [31:0] de_shifter_src2_reg;
    reg [1:0]  de_shifter_op_reg;
    reg        de_is_alu_op_reg;
    reg        de_is_shifter_op_reg;
    reg        de_mem_read_reg;
    reg        de_mem_write_reg;
    reg [2:0]  de_mem_width_reg;
    reg        de_mem_signed_reg;
    reg [31:0] de_store_data_value_reg; // Was idu_store_data_value_out
    reg        de_rf_wen_reg;
    reg [4:0]  de_rf_waddr_reg;         // This is 'rd'

    always @(posedge clk) begin
        if (rst) begin
            de_inst_valid_reg       <= 1'b0;
            de_pc_reg               <= 32'b0;
            de_alu_src1_reg         <= 32'b0;
            de_alu_src2_reg         <= 32'b0;
            de_alu_op_reg           <= 3'b0; // Benign ALU op
            de_shifter_src1_reg     <= 32'b0;
            de_shifter_src2_reg     <= 32'b0;
            de_shifter_op_reg       <= 2'b0; // Benign shifter op
            de_is_alu_op_reg        <= 1'b0;
            de_is_shifter_op_reg    <= 1'b0;
            de_mem_read_reg         <= 1'b0;
            de_mem_write_reg        <= 1'b0;
            de_mem_width_reg        <= 3'b0;
            de_mem_signed_reg       <= 1'b0;
            de_store_data_value_reg <= 32'b0;
            de_rf_wen_reg           <= 1'b0;
            de_rf_waddr_reg         <= 5'b0;
        end else if (pipeline_advance_enable) begin
            if (ld_use_hazard_stall) begin // Insert Bubble
                de_inst_valid_reg       <= 1'b0;
                // Set other controls to NOP values
                de_rf_wen_reg           <= 1'b0;
                de_mem_read_reg         <= 1'b0;
                de_mem_write_reg        <= 1'b0;
                de_is_alu_op_reg        <= 1'b0; // Or make it a NOP operation
                de_is_shifter_op_reg    <= 1'b0;
                // de_alu_op_reg etc. can be don't care or NOP
            end else begin
                de_inst_valid_reg       <= fd_inst_valid_reg;
                de_pc_reg               <= fd_pc_reg;
                de_alu_src1_reg         <= idu_alu_src1_out;
                de_alu_src2_reg         <= idu_alu_src2_out;
                de_alu_op_reg           <= idu_alu_op_out;
                de_shifter_src1_reg     <= idu_shifter_src1_out;
                de_shifter_src2_reg     <= idu_shifter_src2_out;
                de_shifter_op_reg       <= idu_shifter_op_out;
                de_is_alu_op_reg        <= idu_is_alu_op_out;
                de_is_shifter_op_reg    <= idu_is_shifter_op_out;
                de_mem_read_reg         <= idu_mem_read_out;
                de_mem_write_reg        <= idu_mem_write_out;
                de_mem_width_reg        <= idu_mem_width_out;
                de_mem_signed_reg       <= idu_mem_signed_out;
                de_store_data_value_reg <= idu_store_data_value_out;
                de_rf_wen_reg           <= idu_rf_wen_out;
                de_rf_waddr_reg         <= idu_rf_waddr_out;
            end
        end
    end

    //--------------------------------------------------------------------------
    // EX Stage Wires (Outputs from EXU)
    //--------------------------------------------------------------------------
    wire [31:0] exu_alu_result_out;
    wire [31:0] exu_shift_result_out;

    //--------------------------------------------------------------------------
    // EX/MEM Pipeline Register (Internal: em_..._reg)
    //--------------------------------------------------------------------------
    reg [31:0] em_pc_reg;
    reg        em_inst_valid_reg;
    reg [31:0] em_result_reg;             // Result from ALU or Shifter
    reg [31:0] em_store_data_value_reg;   // Data for store (passed from DE)
    reg        em_mem_read_reg;
    reg        em_mem_write_reg;
    reg [2:0]  em_mem_width_reg;
    reg        em_mem_signed_reg;
    reg        em_rf_wen_reg;
    reg [4:0]  em_rf_waddr_reg;           // rd

    always @(posedge clk) begin
        if (rst) begin
            em_inst_valid_reg       <= 1'b0;
            em_pc_reg               <= 32'b0;
            em_result_reg           <= 32'b0;
            em_store_data_value_reg <= 32'b0;
            em_mem_read_reg         <= 1'b0;
            em_mem_write_reg        <= 1'b0;
            em_mem_width_reg        <= 3'b0;
            em_mem_signed_reg       <= 1'b0;
            em_rf_wen_reg           <= 1'b0;
            em_rf_waddr_reg         <= 5'b0;
        end else if (pipeline_advance_enable) begin
            em_inst_valid_reg       <= de_inst_valid_reg;
            em_pc_reg               <= de_pc_reg;
            // Select result from ALU or Shifter
            if (de_is_alu_op_reg) begin
                em_result_reg       <= exu_alu_result_out;
            end else if (de_is_shifter_op_reg) begin
                em_result_reg       <= exu_shift_result_out;
              end else if (de_mem_read_reg || de_mem_write_reg) begin // For Load/Store, ALU result is address
                em_result_reg       <= exu_alu_result_out;
              end else begin // Default, or for other instruction types like U-type
                em_result_reg       <= exu_alu_result_out; // Or handle based on other controls
              end
            em_store_data_value_reg <= de_store_data_value_reg;
            em_mem_read_reg         <= de_mem_read_reg;
            em_mem_write_reg        <= de_mem_write_reg;
            em_mem_width_reg        <= de_mem_width_reg;
            em_mem_signed_reg       <= de_mem_signed_reg;
            em_rf_wen_reg           <= de_rf_wen_reg;
            em_rf_waddr_reg         <= de_rf_waddr_reg;
        end
    end

    //--------------------------------------------------------------------------
    // MEM Stage Wires (Output from MEMU)
    //--------------------------------------------------------------------------
    wire [31:0] memu_rf_wdata_out; // Data from MEMU to be written back or passed through

    //--------------------------------------------------------------------------
    // MEM/WB Pipeline Register (Internal: mw_..._reg)
    //--------------------------------------------------------------------------
    reg [31:0] mw_pc_reg;
    reg        mw_inst_valid_reg;
    reg [31:0] mw_data_to_wb_reg; // Data to be written to RF (from MEMU)
    reg        mw_rf_wen_reg;
    reg [4:0]  mw_rf_waddr_reg;   // rd

    always @(posedge clk) begin
        if (rst) begin
            mw_inst_valid_reg   <= 1'b0;
            mw_pc_reg           <= 32'b0;
            mw_data_to_wb_reg   <= 32'b0;
            mw_rf_wen_reg       <= 1'b0;
            mw_rf_waddr_reg     <= 5'b0;
        end else if (pipeline_advance_enable) begin
            mw_inst_valid_reg   <= em_inst_valid_reg;
            mw_pc_reg           <= em_pc_reg;
            mw_data_to_wb_reg   <= memu_rf_wdata_out;
            mw_rf_wen_reg       <= em_rf_wen_reg;
            mw_rf_waddr_reg     <= em_rf_waddr_reg;
        end
    end

    //--------------------------------------------------------------------------
    // WB Stage: Assign signals to RegFile write ports and WBU inputs
    //--------------------------------------------------------------------------

    assign wb_rf_wen_internal   = mw_rf_wen_reg && mw_inst_valid_reg && pipeline_advance_enable; // this ensures only one write operation each time
    assign wb_rf_waddr_internal = mw_rf_waddr_reg;
    assign wb_rf_wdata_internal = mw_data_to_wb_reg;

    //--------------------------------------------------------------------------
    // Forwarding Unit (FWDU / BPU)
    //--------------------------------------------------------------------------
    wire fwdu_ex_writes_reg  = de_rf_wen_reg && de_inst_valid_reg;
    wire fwdu_mem_writes_reg = em_rf_wen_reg && em_inst_valid_reg;
    wire fwdu_wb_writes_reg  = mw_rf_wen_reg && mw_inst_valid_reg;

    fwdu fwdu_inst (
        .RF_rdata1      (rf_read_data1_raw_internal),    // Raw from RegFile
        .RF_rdata2      (rf_read_data2_raw_internal),    // Raw from RegFile
        .ID_rs1         (idu_rs1_for_hazard_out),        // rs1 addr from IDU
        .ID_rs2         (idu_rs2_for_hazard_out),        // rs2 addr from IDU
        .EX_rd          (fwdu_ex_writes_reg ? de_rf_waddr_reg : 5'b0), // rd from DE reg (if EX writes)
        .MEM_rd         (fwdu_mem_writes_reg ? em_rf_waddr_reg : 5'b0),// rd from EM reg (if MEM writes)
        .WB_rd          (fwdu_wb_writes_reg ? mw_rf_waddr_reg : 5'b0), // rd from MW reg (if WB writes)

        // Data sources for forwarding:
        .EX_alu_result  (de_is_alu_op_reg ? exu_alu_result_out :         // If ALU op in EX, use ALU out
                         de_is_shifter_op_reg ? exu_shift_result_out : // If Shift op in EX, use Shifter out
                         (de_mem_read_reg || de_mem_write_reg) ? exu_alu_result_out : // For L/S in EX, EX_alu_result is addr
                         exu_alu_result_out), // Default to EXU's ALU output for other cases (e.g. U-type)

        .MEM_alu_result (memu_rf_wdata_out), // Result from MEM stage (load data or pass-through ALU result)
                                             // This is the output of MEMU *before* MEM/WB reg
        .WB_RF_wdata    (mw_data_to_wb_reg), // Data from MEM/WB register (final value for WB)

        .fwdu_src1      (idu_final_operand1_in), // Output to IDU
        .fwdu_src2      (idu_final_operand2_in)  // Output to IDU
    );

    //--------------------------------------------------------------------------
    // Control Unit (CU) - Simplified Hazard Detection and Pipeline Control
    //--------------------------------------------------------------------------
    // Load-Use Hazard: ID needs data that EX is loading
    assign ld_use_hazard_stall = (de_inst_valid_reg && de_mem_read_reg && de_rf_wen_reg) && // EX is a valid load that writes a reg
                                 ( (de_rf_waddr_reg == idu_rs1_for_hazard_out && idu_rs1_for_hazard_out != 0) ||
                                   (de_rf_waddr_reg == idu_rs2_for_hazard_out && idu_rs2_for_hazard_out != 0) ) || 
                                 (em_inst_valid_reg && em_mem_read_reg && em_rf_wen_reg) && // MEM is a valid load that writes a reg
                                 ( (em_rf_waddr_reg == idu_rs1_for_hazard_out && idu_rs1_for_hazard_out != 0) ||
                                   (em_rf_waddr_reg == idu_rs2_for_hazard_out && idu_rs2_for_hazard_out != 0) );

    // Global pipeline advance enable
    assign pipeline_advance_enable = if_stage_ready && mem_stage_ready;
                                     // TODO: Add other stall conditions if any (e.g., structural hazards if IFU/MEMU FSMs are complex)

    //--------------------------------------------------------------------------
    // Instantiate Pipeline Stage Modules
    //--------------------------------------------------------------------------
    wire ifu_IRWrite_out;
    wire ifu_IF_stall_out;
    wire ifu_IW_stall_out;
    ifu ifu_inst (
        .clk                    (clk),
        .rst                    (rst),
        .IR                     (ifu_IR_to_fd_reg),
        .fetched_inst_valid     (ifu_valid_to_fd_reg),
        .PC                     (PC),              // IFU uses current PC
        .Inst_Req_Valid         (Inst_Req_Valid),  // Drive top-level output
        .Inst_Req_Ready         (Inst_Req_Ready),  // From top-level input
        .instruction            (Instruction),     // From top-level input
        .Inst_Valid             (Inst_Valid),      // From top-level input
        .Inst_Ready             (Inst_Ready),      // Drive top-level output
        .next_pc                (next_pc_from_idu_internal),
        .ld_use_harzard         (ld_use_hazard_stall),
        .pipeline_advance_enable(pipeline_advance_enable),
        .IF_Ready               (if_stage_ready),
        .branch_condition_satisfied(idu_branch_condition_out), // For Perf
        .Read_data_Ready        (Read_data_Ready), // For Perf
        .Read_data_Valid        (Read_data_Valid), // For Perf
        .IRWrite                (ifu_IRWrite_out), // For Perf
        .IF_stall               (ifu_IF_stall_out),
        .IW_stall               (ifu_IW_stall_out)
    );

    assign pc_value_at_fetch_time = PC; // Capture PC at fetch time

    wire idu_is_branch_out;
    wire idu_is_jump_out;
    wire idu_is_nop_out;
    idu idu_inst (
        .clk            (clk),
        .rst            (rst),
        .IR             (fd_instruction_reg), // From IF/ID reg
        .pc             (fd_pc_reg),          // From IF/ID reg
        .alu_op         (idu_alu_op_out),
        .alu_src1       (idu_alu_src1_out),
        .alu_src2       (idu_alu_src2_out),
        .shifter_op     (idu_shifter_op_out),
        .shifter_src1   (idu_shifter_src1_out),
        .shifter_src2   (idu_shifter_src2_out),
        .is_alu_operation (idu_is_alu_op_out),
        .is_shifter_operation(idu_is_shifter_op_out),
        .mem_read_internal(idu_mem_read_out),
        .mem_write_internal(idu_mem_write_out),
        .mem_width      (idu_mem_width_out),
        .mem_signed     (idu_mem_signed_out),
        .write_data     (idu_store_data_value_out), // Store data value
        .RF_wen         (idu_rf_wen_out),
        .RF_waddr       (idu_rf_waddr_out),         // rd field
        .next_pc        (next_pc_from_idu_internal), // Calculated next PC for IFU MUX
        .raddr1         (idu_regfile_raddr1_out),   // To RegFile
        .raddr2         (idu_regfile_raddr2_out),   // To RegFile
        .RF_rdata1      (idu_final_operand1_in),    // From FWDU
        .RF_rdata2      (idu_final_operand2_in),    // From FWDU
        .ID_rs1         (idu_rs1_for_hazard_out),   // To FWDU/CU
        .ID_rs2         (idu_rs2_for_hazard_out),   // To FWDU/CU
        .branch_condition_satisfied(idu_branch_condition_out), // For Perf
        .is_branch      (idu_is_branch_out),        // For Perf
        .is_jump        (idu_is_jump_out),          // For Perf
        .is_nop         (idu_is_nop_out)            // For Perf
    );

    exu exu_inst (
        .clk          (clk),
        .rst          (rst),
        .alu_src1     (de_alu_src1_reg),      // From ID/EX reg
        .alu_src2     (de_alu_src2_reg),      // From ID/EX reg
        .alu_op       (de_alu_op_reg),        // From ID/EX reg
        .shifter_src1 (de_shifter_src1_reg),  // From ID/EX reg
        .shifter_src2 (de_shifter_src2_reg),  // From ID/EX reg
        .shifter_op   (de_shifter_op_reg),    // From ID/EX reg
        .alu_result   (exu_alu_result_out),   // To EX/MEM reg & FWDU
        .shift_result (exu_shift_result_out)  // To EX/MEM reg & FWDU
    );

    wire memu_RDW_stall_out;
    memu memu_inst (
        .clk                    (clk),
        .rst                    (rst),
        // Outputs to memory interface (driving top-level ports)
        .MemWrite               (MemWrite),
        .Write_strb             (Write_strb),
        .MemRead                (MemRead),
        .Write_data             (Write_data), // Data to memory bus from MEMU
        // Inputs from memory interface (from top-level ports)
        .Mem_Req_Ready          (Mem_Req_Ready),
        .Read_data              (Read_data),
        .Read_data_Valid        (Read_data_Valid),
        .Read_data_Ready        (Read_data_Ready),
        // Inputs from EX/MEM pipeline register
        .MemRead_bus_in         (em_mem_read_reg),
        .MemWrite_bus_in        (em_mem_write_reg),
        .mem_width              (em_mem_width_reg),
        .mem_signed             (em_mem_signed_reg),
        .RF_rdata2              (em_store_data_value_reg), // Data for store operation
        .alu_result             (em_result_reg),           // Address or ALU data
        // Output to MEM/WB pipeline register
        .RF_wdata               (memu_rf_wdata_out),
        // Pipeline control
        .pipeline_advance_enable(pipeline_advance_enable),
        .mem_ready              (mem_stage_ready),         // To CU
        .mem_stall              (memu_mem_stall_out), // Connect to an internal wire for perf counter
        .RDW_stall              (memu_RDW_stall_out)
    );
    wire memu_mem_stall_out; // Example for connecting perf counter

    wbu wbu_inst (
      .inst_valid (mw_inst_valid_reg),
      .pc         (mw_pc_reg),
      .RF_wen     (wb_rf_wen_internal),
      .RF_waddr   (mw_rf_waddr_reg),
      .RF_wdata   (mw_data_to_wb_reg),
      .inst_retire(inst_retire) // Drive top-level output
    );


    // Address to memory (driven by EX/MEM register's ALU result if it's a mem op)
    // MEMU internal Address is alu_result_from_exmem
    // Top-level Address should be driven by the address calculated in EX and passed to MEM
    assign Address = (em_mem_read_reg || em_mem_write_reg) ? em_result_reg : 32'b0; // Or some default/hold

endmodule


module ifu (
  input clk,
  input rst,

  output reg [31:0] IR,
  output reg        fetched_inst_valid,

  output reg [31:0] PC,
  output            Inst_Req_Valid,
  input             Inst_Req_Ready,

  input      [31:0] instruction,
  input             Inst_Valid,
  output            Inst_Ready,

  input      [31:0] next_pc,

  input             ld_use_harzard,
  input             pipeline_advance_enable,

  output            IF_Ready,

  input             branch_condition_satisfied, // For perf counters
  input             Read_data_Ready, // For perf counters
  input             Read_data_Valid,

  output            IRWrite, // For perf counters
  output            IF_stall,
  output            IW_stall
);

  localparam INIT = 5'b00001;
  localparam IF   = 5'b00010;
  localparam IW   = 5'b00100;
  localparam RDY  = 5'b01000;
  localparam STA  = 5'b10000;

  reg  [4:0] next_state;
  reg  [4:0] current_state;

  wire _ld_use_branch_handler;
  assign _ld_use_branch_handler = branch_condition_satisfied && Read_data_Ready && Read_data_Valid;
  reg ld_use_branch_handler;

  always @(posedge clk) begin
    ld_use_branch_handler <= _ld_use_branch_handler;
  end

  always @(posedge clk) begin
    if (rst)
      current_state <= INIT;
    else
      current_state <= next_state;
  end

  always @(*) begin
    case (current_state)
      INIT : begin
        if (rst) begin
          next_state = INIT;
        end
        else begin
          next_state = IF;
        end
      end
//      IF : begin
//        if (Inst_Req_Ready) begin
//          next_state = IW;
//        end
//        else begin
//          next_state = IF;
//        end
//      end
//      IW : begin
//        if (Inst_Valid) begin
//          next_state = RDY;
//        end
//        else begin
//          next_state = IW;
//        end
//      end
      IF : begin // to boost frequency, this state handles both instruction fetch and stall
        if (Inst_Valid) begin
          next_state = RDY;
        end else begin
          next_state = IF;
        end
      end
      RDY : begin
        if (pipeline_advance_enable) begin
          if (is_sequential_fetch) begin
            next_state = IF;
          end else begin
            next_state = STA;
          end
        end
        else begin
          next_state = RDY;
        end
      end
      STA : begin
        if (!ld_use_harzard) begin
          next_state = IF;
        end
        else begin
          next_state = RDY;
        end
      end
      default :
        next_state = INIT;
    endcase
  end

  // -- FSM Output Logic --
  wire pc_write_enable;
  assign IRWrite = (current_state == IF) && Inst_Valid;
  assign Inst_Req_Valid = (current_state == IF); // Request instruction fetch
  assign Inst_Ready = (current_state == INIT) || (current_state == IF);
  assign IF_Ready = (current_state == RDY);
  assign pc_write_enable = (current_state == STA) && !ld_use_harzard;
  assign pc_write_sequential = (current_state == RDY) && is_sequential_fetch && !ld_use_harzard && pipeline_advance_enable;
  assign IF_stall = (current_state == IF && !Inst_Req_Ready && !rst);
  assign IW_stall = (current_state == IW && !Inst_Valid && !rst);

  wire [ 6:0] opcode;               // Opcode field
  assign opcode = IR[6:0];
  wire is_sequential_fetch;
  assign is_sequential_fetch = !(opcode == 7'b1101111) && // JAL
                               !(opcode == 7'b1100111) && // JALR
                               !(opcode == 7'b1100011);   // Store
  wire [31:0] sequential_next_pc;
  assign sequential_next_pc = PC + 4; // Sequential fetch is just PC + 4

  always @(posedge clk) begin
    if (rst) begin
      PC <= 32'b0;
    end
    else if (pc_write_sequential) begin
      PC <= sequential_next_pc;
    end
    else if (pc_write_enable || ld_use_branch_handler) begin
      PC <= next_pc;
    end
  end

  always @(posedge clk) begin
    if (rst) begin
      IR <= 32'b0;
      fetched_inst_valid <= 0;
    end
    else if (current_state == IF && Inst_Valid) begin
      IR <= instruction;
      fetched_inst_valid <= 1'b1;
    end
  end
endmodule

module idu (
  input clk,
  input rst,

  input  [31:0] IR,
  input  [31:0] pc,

  output [ 2:0] alu_op,
  output [31:0] alu_src1,
  output [31:0] alu_src2,
  output [ 1:0] shifter_op,
  output [31:0] shifter_src1,
  output [31:0] shifter_src2,
  output        is_alu_operation,
  output        is_shifter_operation,

  output        mem_read_internal,
  output        mem_write_internal,
  output [ 2:0] mem_width,
  output        mem_signed,
  output [31:0] write_data,

  output        RF_wen,
  output [ 4:0] RF_waddr,

  output [31:0] next_pc,

  output [ 4:0] raddr1,
  output [ 4:0] raddr2,
  input  [31:0] RF_rdata1,
  input  [31:0] RF_rdata2,

  output [ 4:0] ID_rs1,
  output [ 4:0] ID_rs2,

  output        branch_condition_satisfied, // for perf counters
  output        is_branch, // for perf counters
  output        is_jump,   // for perf counters
  output        is_nop     // for perf counters
);

  //----------------------------------------------------------------------------
  // Parameter Definitions
  // (Grouped here for clarity, used across stages)
  //----------------------------------------------------------------------------

    // ALU Operation Code Definitions
    localparam ALU_AND  = 3'b000;
    localparam ALU_OR   = 3'b001;
    localparam ALU_ADD  = 3'b010;
    localparam ALU_SLTU = 3'b011; // Set Less Than Unsigned
    localparam ALU_XOR  = 3'b100;
    localparam ALU_SUB  = 3'b110;
    localparam ALU_SLT  = 3'b111; // Set Less Than (Signed)

    // Codes used to indicate operation is handled by shifter, not main ALU path for result
    localparam ALU_SLL  = 3'b000; // Logical Shift Left
    localparam ALU_SRL  = 3'b000; // Logical Shift Right
    localparam ALU_SRA  = 3'b000; // Arithmetic Shift Right
    localparam ALU_XXX  = 3'b000; // Undefined or Don't Care ALU operation

    // Shifter Operation Code Definitions
    localparam SHIFT_NONE = 2'b01; // No shift operation
    localparam SHIFT_SLL  = 2'b00; // Logical Shift Left
    localparam SHIFT_SRL  = 2'b10; // Logical Shift Right
    localparam SHIFT_SRA  = 2'b11; // Arithmetic Shift Right

  // -- Signals generated in ID (purely from Instruction) --
  wire [ 6:0] opcode;               // Opcode field
  wire [ 2:0] funct3;               // Funct3 field
  wire [ 6:0] funct7;               // Funct7 field
  wire [ 4:0] rs1;                  // Source register 1
  wire [ 4:0] rs2;                  // Source register 2
  wire [ 4:0] rd;                   // Destination register
  wire [31:0] current_pc;           // Current PC value
  wire [31:0] imm_I;                // Immediate value (I-type)
  wire [31:0] imm_S;                // Immediate value (S-type)
  wire [31:0] imm_B;                // Immediate value (B-type)
  wire [31:0] imm_U;                // Immediate value (U-type)
  wire [31:0] imm_J;                // Immediate value (J-type)
  wire [31:0] imm;                  // Immediate value (seleted based on instruction type)

  wire is_OPIMM;                    // Is it an OP-IMM instruction?
  wire is_addi;                     // Is it an ADDI instruction?
  wire is_ebreak;                   // Is it an EBREAK instruction?
  wire is_load;                     // Is it a load instruction?
  wire is_jalr;                     // Is it a JALR instruction?
  wire is_lui;                      // Is it a LUI instruction?
  wire is_auipc;                    // Is it an AUIPC instruction?
  wire is_I;                        // Is it an I-type instruction?
  wire is_S;                        // Is it an S-type instruction?
  wire is_B;                        // Is it a B-type instruction?
  wire is_U;                        // Is it a U-type instruction?
  wire is_J;                        // Is it a J-type instruction?
  wire is_R;                        // Is it an R-type instruction?

  //============================================================================
  // PIPELINE STAGE 2: Instruction Decode / Register Fetch (ID)
  //============================================================================

  // -- Instruction Field Decoding --
  assign      opcode   = IR[ 6: 0]; // Opcode field
  assign      funct3   = IR[14:12]; // Funct3 field
  assign      funct7   = IR[31:25]; // Funct7 field
  assign      rs1      = IR[19:15]; // Source register 1
  assign      rs2      = IR[24:20]; // Source register 2
  assign      rd       = IR[11: 7]; // Destination register
  assign      RF_waddr = rd;        // Register file write address

  // -- Immediate type decoding --
  assign      imm_I    = {{20{IR[31]}}, IR[31:20]};                          // Immediate value (I-type)
  assign      imm_S    = {{20{IR[31]}}, IR[31:25], IR[11:7]};                // Immediate value (S-type)
  assign      imm_B    = {{20{IR[31]}}, IR[7], IR[30:25], IR[11:8], 1'b0};   // Immediate value (B-type)
  assign      imm_U    = {IR[31:12], 12'b0};                                 // Immediate value (U-type)
  assign      imm_J    = {{12{IR[31]}}, IR[19:12], IR[20], IR[30:21], 1'b0}; // Immediate value (J-type)
  assign      imm      = (is_I) ? imm_I :
                         (is_S) ? imm_S :
                         (is_B) ? imm_B :
                         (is_U) ? imm_U :
                         (is_J) ? imm_J : 32'b0; // Default immediate value

  // -- Instruction Type Decoding --
  assign      is_OPIMM = (opcode == 7'b0010011); // OP-IMM instruction
  assign      is_addi  = (opcode == 7'b0010011) && (funct3 == 3'b000); // ADDI instruction
  assign      is_ebreak = (opcode == 7'b1110011) && (funct3 == 3'b000) && (IR[31:20] == 12'b000000000001); // EBREAK instruction
  assign      is_load  = (opcode == 7'b0000011); // Load instruction
  assign      is_jalr  = (opcode == 7'b1100111); // JALR instruction
  assign      is_lui   = (opcode == 7'b0110111); // LUI instruction
  assign      is_auipc = (opcode == 7'b0010111); // AUIPC instruction
  assign      is_nop   = (IR    == 32'h00000013); // NOP instruction

  // -- Control Signals for Instruction Types --
  assign      is_I     = is_OPIMM || is_load || is_jalr; // I-type instruction
  assign      is_S     = (opcode == 7'b0100011);         // S-type instruction
  assign      is_B     = (opcode == 7'b1100011);         // B-type instruction
  assign      is_U     = is_lui || is_auipc;             // U-type instruction
  assign      is_J     = (opcode == 7'b1101111);         // J-type instruction
  assign      is_R     = (opcode == 7'b0110011);         // R-type instruction

  // -- Decode ALU and shifter operations based on instruction type --
  assign alu_src1 = (is_jalr)                      ? current_pc : // For AUIPC, use current PC
                    (is_I || is_R || is_S || is_B) ? RF_rdata1  : // rs1 for most operations
                    (is_J)                         ? current_pc : // PC for JAL offset calculation
                    (is_lui)                       ? 32'b0      : // Zero for LUI (0 + imm)
                    (is_auipc)                     ? current_pc : // PC for AUIPC (PC + imm)
                                                     32'b0;       // Default to zero

  assign alu_src2 = (is_jalr)         ? 4            : // JALR uses 4 for address calculation
                    (is_I)            ? imm          : // Immediate for I-types (incl. JALR) and J-type (JAL)
                    (is_J)            ? 4            : // JALR stores pc + 4 in rd
                    (is_R)            ? RF_rdata2    : // rs2 for R-type operations
                    (is_S)            ? imm          : // Immediate for S-type (store address calculation)
                    (is_B)            ? RF_rdata2    : // rs2 for B-type (branch comparison)
                    (is_U)            ? imm          : // Immediate for U-type (LUI/AUIPC)
                                        32'b0;         // Default to zero

  assign shifter_src1 = RF_rdata1;                        // Source for shift operations is always rs1
  assign shifter_src2 = (is_R) ? RF_rdata2      :         // R-type shifts use lower 5 bits of rs2
                        (is_I) ? imm            :         // I-type shifts use lower 5 bits of immediate (shamt)
                                 32'b0;                    // Default

  // Control Signals for ALU and Shifter
  wire funct7_5 = funct7[5]; // Bit 5 of funct7 (differentiates ADD/SUB, SRL/SRA)

  // ALU Operation (alu_op) Selection Logic
  assign alu_op =
      is_R ? // R-Type instructions (opcode: 0110011)
          (funct3 == 3'b000 ? (funct7_5 ? ALU_SUB : ALU_ADD)  : // ADD/SUB
           funct3 == 3'b001 ? ALU_SLL                         : // SLL (handled by shifter)
           funct3 == 3'b010 ? ALU_SLT                         : // SLT
           funct3 == 3'b011 ? ALU_SLTU                        : // SLTU
           funct3 == 3'b100 ? ALU_XOR                         : // XOR
           funct3 == 3'b101 ? (funct7_5 ? ALU_SRA : ALU_SRL)  : // SRL/SRA (handled by shifter)
           funct3 == 3'b110 ? ALU_OR                          : // OR
           funct3 == 3'b111 ? ALU_AND                         : // AND
                              ALU_XXX) :                        // Default for unknown R-type funct3
      is_OPIMM ? // I-Type OP-IMM instructions (opcode: 0010011)
          (funct3 == 3'b000 ? ALU_ADD                         : // ADDI
           funct3 == 3'b001 ? ALU_SLL                         : // SLLI (handled by shifter)
           funct3 == 3'b010 ? ALU_SLT                         : // SLTI
           funct3 == 3'b011 ? ALU_SLTU                        : // SLTIU
           funct3 == 3'b100 ? ALU_XOR                         : // XORI
           funct3 == 3'b101 ? (funct7_5 ? ALU_SRA : ALU_SRL)  : // SRLI/SRAI (handled by shifter)
           funct3 == 3'b110 ? ALU_OR                          : // ORI
           funct3 == 3'b111 ? ALU_AND                         : // ANDI
                              ALU_XXX) :                        // Default for unknown OP-IMM funct3
      // Address calculation for Load/Store, or value formation for U-types, J-types
      (is_load || is_S || is_lui || is_auipc || is_J || is_jalr) ? ALU_ADD :
      is_B ? // B-Type branch instructions (opcode: 1100011) - ALU used for comparison
          (funct3 == 3'b000 ? ALU_SUB  : // BEQ (compare for equality via subtraction)
           funct3 == 3'b001 ? ALU_SUB  : // BNE (compare for inequality via subtraction)
           funct3 == 3'b100 ? ALU_SLT  : // BLT
           funct3 == 3'b101 ? ALU_SLT  : // BGE (operands flipped for SLT or check !N)
           funct3 == 3'b110 ? ALU_SLTU : // BLTU
           funct3 == 3'b111 ? ALU_SLTU : // BGEU (operands flipped for SLTU or check !N)
                              ALU_XXX) : // Default for unknown B-type funct3
      ALU_XXX; // Default for any other unhandled instruction type

  // Determine if the current operation is a shift
  wire is_shift_funct3 = (funct3 == 3'b001) || // SLL, SLLI
                         (funct3 == 3'b101);   // SRL, SRLI, SRA, SRAI

  // Signal indicating the instruction's result comes from the shifter unit
  assign is_shifter_operation = (is_R && is_shift_funct3) ||   // R-type shifts
                                (is_OPIMM && is_shift_funct3); // I-type (OP-IMM) shifts

  // Shifter Operation (shifter_op) Selection Logic
  assign shifter_op = is_shifter_operation ?
                          (funct3 == 3'b001 ? SHIFT_SLL :                  // SLL / SLLI
                          (funct7_5         ? SHIFT_SRA : SHIFT_SRL)) :    // SRA / SRAI or SRL / SRLI
                          SHIFT_NONE;                                      // Default: No shift

  // Signal indicating the instruction's result comes from the main ALU path
  // (and is not primarily a shifter operation for its final result)
  wire uses_alu_for_result_or_calc = is_R || is_OPIMM || is_load || is_S || is_B ||
                                     is_lui || is_auipc || is_J || is_jalr;
  assign is_alu_operation = uses_alu_for_result_or_calc && !is_shifter_operation;

  // branch and jump
  assign current_pc = pc;
  // Branch Target Address Calculation
  wire [31:0] branch_target = current_pc + imm_B;

  // calculate branch conditions in ID stage
  wire equal = (RF_rdata1 == RF_rdata2); // Equality check for branch conditions
  wire ltu  = (RF_rdata1 < RF_rdata2); // Less than check for branch conditions
  wire lts  = ($signed(RF_rdata1) < $signed(RF_rdata2)); // Signed less than check for branch conditions

  // Branch Condition Satisfied Logic
  assign branch_condition_satisfied = (is_B ?
                                      // Check funct3 to determine the specific branch condition
                                      ( (funct3 == 3'b000) ? equal                 : // BEQ: branch if (rs1 == rs2) -> Zero flag is set by (rs1 - rs2)
                                        (funct3 == 3'b001) ? !equal                : // BNE: branch if (rs1 != rs2) -> Zero flag is not set
                                        (funct3 == 3'b100) ? lts                   : // BLT: branch if (rs1 < rs2) signed -> SLT result is 1
                                        (funct3 == 3'b101) ? !lts                  : // BGE: branch if (rs1 >= rs2) signed -> SLT result is 0
                                        (funct3 == 3'b110) ? ltu                   : // BLTU: branch if (rs1 < rs2) unsigned -> SLTU result is 1
                                        (funct3 == 3'b111) ? !ltu                  : // BGEU: branch if (rs1 >= rs2) unsigned -> SLTU result is 0
                                                             1'b0                    // Default: Should not happen for valid B-type funct3
                                      ) :
                                      1'b0);

  // Jump Target Address Calculation
  wire [31:0] jump_target = (is_J)    ? current_pc + imm_J : // JAL: PC + immediate
                            (is_jalr) ? ((RF_rdata1 + imm_I) & 32'hFFFFFFFE) : // JALR: Align to 2-byte boundary
                            32'b0;                                    // Default: Not a jump instruction, so target is not calculated.
  // -- PC Update Logic --
  assign      next_pc     = (is_J || is_jalr) ? jump_target :         // Use jump target for JAL/JALR
                            (is_B && branch_condition_satisfied) ? branch_target : // Use branch target if condition is satisfied
                            current_pc + 4;                           // Default: PC + 4 for normal instruction flow

  // mem_read and mem_write logic
  assign mem_read_internal  = is_load; // Load instructions
  assign mem_write_internal = is_S;   // Store instructions

  // mem_signed logic
  assign mem_signed = !funct3[2];

  // mem_width logic
  assign mem_width = (is_load || is_S) ? // Load/Store instructions
                          (funct3 == 3'b000 ? 3'b001 : // LB/LBU
                           funct3 == 3'b001 ? 3'b010 : // LH/LHU
                           funct3 == 3'b010 ? 3'b100 : // LW
                           funct3 == 3'b100 ? 3'b001 : // SB
                           funct3 == 3'b101 ? 3'b010 : // SH
                           funct3 == 3'b110 ? 3'b100 : // SW
                           3'b000) : // Default: No memory operation
                           3'b000; // Default: No memory operation

  assign      RF_wen             = (is_I || is_R || is_J || is_U) && (rd != 0);

  // assign ID_rs signals
  assign ID_rs1 = rs1; // Source register 1
  assign ID_rs2 = rs2; // Source register 2

  // assign raddr signals for register file access
  assign raddr1 = rs1; // Register file read address 1
  assign raddr2 = rs2; // Register file read address 2

  // assign write_data for store operations
  assign write_data = (is_S) ? RF_rdata2 : // Store data for S-type instructions
                            (is_I || is_R || is_J || is_U) ? RF_rdata1 : // Data for I, R, J, U types
                            32'b0; // Default: No data to write

  // assign is_branch for perf counters
  assign is_branch = is_B;

  // assign is_jump for perf counters
  assign is_jump = (is_J || is_jalr);
endmodule

// exu does not account for whether this is an alu or shifter operation
// so these two signals need to be passed to future modules
module exu (
  input         clk,
  input         rst,

  input  [31:0] alu_src1,
  input  [31:0] alu_src2,
  input  [ 2:0] alu_op,

  input  [31:0] shifter_src1,
  input  [31:0] shifter_src2,
  input  [ 1:0] shifter_op,

  output [31:0] alu_result,
  output [31:0] shift_result
);

  alu instance_alu (
      .A          (alu_src1),         // Input A from Src Sel
      .B          (alu_src2),         // Input B from Src Sel
      .ALUop      (alu_op),           // Input Opcode from Op Gen
      .Overflow   (),
      .CarryOut   (),
      .Zero       (),                 // Output: Zero flag -> To EX (PC Ctrl), WB
      .Result     (alu_result)        // Output: ALU computation result -> To EX (PC Ctrl), MEM, WB
  );

  shifter instance_shifter (
      .A          (shifter_src1),         // Input Data from Src Sel
      .B          (shifter_src2[4:0]),         // Input Shift Amount from Src Sel
      .Shiftop    (shifter_op),           // Input Opcode from ID
      .Result     (shift_result)          // Output: Shifter result -> To WB
  );

endmodule

module memu (
  input clk,
  input rst,

  output        MemWrite,
  output [ 3:0] Write_strb,
  output        MemRead,
  input         Mem_Req_Ready,

  input  [31:0] Read_data,
  input         Read_data_Valid,
  output        Read_data_Ready,

  input         MemRead_bus_in,
  input         MemWrite_bus_in,
  input  [2:0]  mem_width,
  input         mem_signed,

  input  [31:0] RF_rdata2,
  output [31:0] Write_data,

  input  [31:0] alu_result,

  output [31:0] RF_wdata,

  input         pipeline_advance_enable,
  output        mem_ready,

  output        mem_stall, // for perf counters
  output        RDW_stall
);

  localparam IDLE = 5'b00001, // Initial state
             LD  = 5'b00010,
             RDW = 5'b00100,
             ST  = 5'b01000,
             RDY = 5'b10000;

  reg  [4:0] current_state;
  wire [4:0] next_state;

  always @(posedge clk) begin
    if (rst) begin
      current_state <= RDY;
    end else begin
      current_state <= next_state;
    end
  end

  assign  next_state =
      (current_state == LD)  ? (Mem_Req_Ready ? RDW : LD)     :
      (current_state == RDW) ? (Read_data_Valid ? RDY : RDW) :
      (current_state == ST)  ? (Mem_Req_Ready ? RDY : ST)    :
      (current_state == RDY) ? (pipeline_advance_enable ? IDLE : RDY) :
      (current_state == IDLE) ? (
          MemRead_bus_in           ? LD  :
          MemWrite_bus_in          ? ST  :
                                     RDY
      ) :
      RDY;

  assign MemWrite = (current_state == ST);
  assign MemRead  = (current_state == LD);
  assign Read_data_Ready = (current_state == RDW);
  assign mem_ready = (current_state == RDY);
  assign mem_stall = ((current_state == LD || current_state == ST) && !Mem_Req_Ready && !rst);
  assign RDW_stall = (current_state == RDW && !Read_data_Valid && !rst);

  //============================================================================
  // PIPELINE STAGE 4: Memory Access (MEM)
  //============================================================================

  wire [31:0] Address;                                                // Address for load/store operations
  assign      Address     = alu_result;   // Address for load/store operations
  wire [ 1:0] addr_offset = Address[1:0];                             // Address offset for load/store operations
  wire        addr_0      = (addr_offset == 2'b00);
  wire        addr_1      = (addr_offset == 2'b01);
  wire        addr_2      = (addr_offset == 2'b10);
  wire        addr_3      = (addr_offset == 2'b11);
  wire        width_SB   = (mem_width == 3'b001); // Store Byte
  wire        width_SH   = (mem_width == 3'b010); // Store Halfword
  wire        width_SW   = (mem_width == 3'b100); // Store Word
  wire        width_LB   = (mem_width == 3'b001); // Load Byte
  wire        width_LH   = (mem_width == 3'b010); // Load Halfword
  wire        width_LW   = (mem_width == 3'b100); // Load Word
  wire        width_LBU  = (mem_width == 3'b001); // Load Byte Unsigned
  wire        width_LHU  = (mem_width == 3'b010); // Load Halfword Unsigned

  // Memory Write Strobe Generation (Uses ID signals, EX result offset)
  assign      Write_strb  = {4{MemWrite}} & ( // Use is_store (mem_write_internal) from ID
                              (({4{width_SB}} & ((addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0010 : 0) | (addr_2 ? 4'b0100 : 0) | (addr_3 ? 4'b1000 : 0))) | // SB
                              ({4{width_SH}} & ((addr_0 ? 4'b0011 : 0) | (addr_2 ? 4'b1100 : 0))) |                                                    // SH
                              ({4{width_SW}} & (addr_0 ? 4'b1111 : 4'b0000))                                                                           // SW
                             )); // -> To Memory Interface

  assign      Write_data  = {32{MemWrite}} & ( // Format RF_rdata2 for stores -> To Memory Interface
                              (({32{width_SB}} & {4{RF_rdata2[7:0]}}) | // SB
                              ({32{width_SH}} & {2{RF_rdata2[15:0]}}) | // SH
                              ({32{width_SW}} & RF_rdata2)              // SW
                            ));

  wire [31:0] _load_data; // Data loaded from memory, to be passed to WB stage
  reg  [31:0] load_data; // Register to hold the load data
  assign      _load_data          = (current_state == RDW && Read_data_Valid) ? // Process Read_data -> To WB Stage
                                    ( (width_LB || width_LBU) ?  // LB/LBU
                                      (addr_0 ? {{24{(mem_signed & Read_data [ 7])}}, Read_data [ 7: 0]} :
                                       addr_1 ? {{24{(mem_signed & Read_data [15])}}, Read_data [15: 8]} :
                                       addr_2 ? {{24{(mem_signed & Read_data [23])}}, Read_data [23:16]} :
                                                {{24{(mem_signed & Read_data [31])}}, Read_data [31:24]} )

                                    : (width_LH || width_LHU) ?  // LH/LHU
                                      (addr_0 ? {{16{(mem_signed & Read_data [15])}}, Read_data [15: 0]} :
                                       addr_2 ? {{16{(mem_signed & Read_data [31])}}, Read_data [31:16]} :
                                                32'b0 )

                                    : (width_LW) ? Read_data // LW

                                    : 32'b0 ) // Default unknown load
                                    : 32'b0;  // Default if not a load

  always @(posedge clk) begin
    if (Read_data_Valid) begin
      load_data <= _load_data; // only update load_data when Read_data is valid
    end else begin
      load_data <= load_data;
    end
  end

  assign RF_wdata = MemRead_bus_in ? load_data : alu_result;
endmodule

module wbu (
  input         inst_valid,
  input  [31:0] pc,
  input         RF_wen,
  input  [ 4:0] RF_waddr,
  input  [31:0] RF_wdata,

  output [69:0] inst_retire
);

  assign inst_retire = {70{inst_valid}} & {RF_wen, RF_waddr, RF_wdata, pc};

endmodule

module fwdu (
  input  [31:0] RF_rdata1,
  input  [31:0] RF_rdata2,

  input  [ 4:0] ID_rs1,
  input  [ 4:0] ID_rs2,
  input  [ 4:0] EX_rd,  // future value of rd is about to be calculated in the EX stage
  input  [ 4:0] MEM_rd, // value of rd is about to be passed the MEM stage
  input  [ 4:0] WB_rd,  // value of rd is about to be written in the WB stage

  input  [31:0] EX_alu_result,
  input  [31:0] MEM_alu_result,
  input  [31:0] WB_RF_wdata,

  output [31:0] fwdu_src1,
  output [31:0] fwdu_src2
);

    /* conditions of different bypass */
    wire ex_bp1, ex_bp2, mem_bp1, mem_bp2, wb_bp1, wb_bp2;

    /* the "0" register doesn't matter */
    assign  ex_bp1 = (ID_rs1 ==  EX_rd) && ( |EX_rd[4:0]);
    assign  ex_bp2 = (ID_rs2 ==  EX_rd) && ( |EX_rd[4:0]);
    assign mem_bp1 = (ID_rs1 == MEM_rd) && (|MEM_rd[4:0]);
    assign mem_bp2 = (ID_rs2 == MEM_rd) && (|MEM_rd[4:0]);
    assign  wb_bp1 = (ID_rs1 ==  WB_rd) && ( |WB_rd[4:0]);
    assign  wb_bp2 = (ID_rs2 ==  WB_rd) && ( |WB_rd[4:0]);


    /* EX bypass is prior to MEM bypass, so as MEM to WB */

    assign fwdu_src1 = ex_bp1  ? EX_alu_result  :
                   mem_bp1 ? MEM_alu_result :
                   wb_bp1  ? WB_RF_wdata    :
                   RF_rdata1;

    assign fwdu_src2 = ex_bp2  ? EX_alu_result  :
                   mem_bp2 ? MEM_alu_result :
                   wb_bp2  ? WB_RF_wdata    :
                   RF_rdata2;

endmodule

