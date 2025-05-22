`timescale 10ns / 1ns

module custom_cpu (
    input clk,
    input rst,

    //Instruction request channel
    output [31:0] PC,
    output        Inst_Req_Valid,
    input         Inst_Req_Ready,

    //Instruction response channel
    input  [31:0] Instruction,
    input         Inst_Valid,
    output        Inst_Ready,

    //Memory request channel
    output [31:0] Address,
    output        MemWrite,
    output [31:0] Write_data,
    output [ 3:0] Write_strb,
    output        MemRead,
    input         Mem_Req_Ready,

    //Memory data response channel
    input  [31:0] Read_data,
    input         Read_data_Valid,
    output        Read_data_Ready,

    input intr,

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

    output [69:0] inst_retire
);


  // TODO: Please add your custom CPU code here

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


  //----------------------------------------------------------------------------
  // Internal Wires - Connecting Logic Blocks and Modules
  // (Grouped here for clarity, used across stages)
  //----------------------------------------------------------------------------

  // -- Signals generated in ID (purely from Instruction) --
  wire [ 6:0] opcode;               // Opcode field
  wire [ 2:0] funct3;               // Funct3 field
  wire [ 6:0] funct7;               // Funct7 field
  wire [ 4:0] rs1;                  // Source register 1
  wire [ 4:0] rs2;                  // Source register 2
  wire [ 4:0] rd;                   // Destination register
  wire [31:0] current_pc;           // Current PC value
  wire [31:0] next_pc;              // Next PC value
  wire [31:0] imm_I;                // Immediate value (I-type)
  wire [31:0] imm_S;                // Immediate value (S-type)
  wire [31:0] imm_B;                // Immediate value (B-type)
  wire [31:0] imm_U;                // Immediate value (U-type)
  wire [31:0] imm_J;                // Immediate value (J-type)
  wire [31:0] imm;                  // Immediate value (seleted based on instruction type)
  reg  [ 8:0] current_state;        // Current state of the FSM
  reg  [ 8:0] next_state;           // Next state of the FSM
  reg  [31:0] IR;                   // Instruction Register

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

  // -- Signals for Register File --
  wire [31:0] RF_rdata1;
  wire [31:0] RF_rdata2;

  //-- Signals from ALU/Shifter Path (Generated in EX) --
  wire [31:0] alu_src1;               // First ALU operand
  wire [31:0] alu_src2;               // Second ALU operand
  wire [31:0] shifter_src1;           // First Shifter operand (data)
  wire [31:0] shifter_src2;           // Second Shifter operand (shift amount)
  wire [ 2:0] alu_op;                 // Final ALU operation control to ALU
  wire        alu_zero;               // ALU Zero flag
  wire [ 1:0] shifter_op;             // Final shifter operation control to shifter
  reg  [31:0] alu_result;             // ALU computation result
  reg  [31:0] shift_result;           // Shifter result

  //-- Signals from Memory Path (Generated in MEM) --
  wire [31:0] load_data;              // Data processed from memory/registers for load operations

  //-- Signals for WB Stage --
  wire        RF_wen;                 // Final write enable to RegFile
  wire [ 4:0] RF_waddr;               // Write address to RegFile
  reg  [31:0] RF_wdata;               // Write data to RegFile

/* The following signal is leveraged for behavioral simulation,
* which is delivered to testbench.
*
* STUDENTS MUST CONTROL LOGICAL BEHAVIORS of THIS SIGNAL.
*
* inst_retired (70-bit): detailed information of the retired instruction,
* mainly including (in order)
* {
*   reg_file write-back enable  (69:69,  1-bit),
*   reg_file write-back address (68:64,  5-bit),
*   reg_file write-back data    (63:32, 32-bit),
*   retired PC                  (31: 0, 32-bit)
* }
*
*/
  assign inst_retire = {RF_wen, RF_waddr, RF_wdata, current_pc}; // Assigning the inst_retire signal with the required information

  //============================================================================
  // PIPELINE STAGE 0: FSM Implementation
  //============================================================================

// -- FSM State Definitions --
localparam INIT = 9'b000000001, // Initial State
           IF   = 9'b000000010, // Instruction Fetch
           IW   = 9'b000000100, // Instruction Wait
           ID   = 9'b000001000, // Instruction Decode
           EX   = 9'b000010000, // Execute
           ST   = 9'b000100000, // Store - Memory Write
           LD   = 9'b001000000, // Load - Memory Read
           RDW  = 9'b010000000, // Read Data Wait
           WB   = 9'b100000000; // Write Back

  // -- FSM State Register --
  always @(posedge clk) begin
    if (rst) begin
      current_state <= INIT;         // Reset state
    end else begin
      current_state <= next_state; // Update state based on FSM logic
    end
  end

  // -- FSM Next State Logic --
  always @(*) begin
    case (current_state)
      INIT : begin
        if (rst) begin
          next_state = INIT; // Reset state
        end
        else begin
          next_state = IF;
        end
      end
      IF : begin
        if (Inst_Req_Ready) begin
          next_state = IW;
        end
        else begin
          next_state = IF;
        end
      end
      IW : begin
        if (Inst_Valid) begin
          next_state = ID;
        end
        else begin
          next_state = IW;
        end
      end
      ID : begin
              next_state = EX;
      end
      EX : begin
        if (is_B) begin
          next_state = IF;
        end
        else if (is_load) begin
          next_state = LD;
        end
        else if (is_R || is_I || is_U || is_J) begin
          next_state = WB;
        end
        else if (is_S) begin
          next_state = ST;
        end
        else if (is_ebreak) begin
          next_state = IF;
        end
        else begin
          next_state = IF;
        end
      end
      LD : begin
        if (Mem_Req_Ready) begin
          next_state = RDW;
        end
        else begin
          next_state = LD;
        end
      end
      RDW : begin
        if (Read_data_Valid) begin
          next_state = WB;
        end
        else begin
          next_state = RDW;
        end
      end
      ST : begin
        if (Mem_Req_Ready) begin
          next_state = IF;
        end
        else begin
          next_state = ST;
        end
      end
      WB : next_state = IF;
      default: next_state = IF;
  endcase
  end

  // -- FSM Output Logic --
  assign IRWrite = (current_state == IW) && Inst_Valid;
  assign Regwrite_fsm = (current_state == WB); // Register write enable signal
  assign Inst_Req_Valid = (current_state == IF); // Request instruction fetch
  assign Inst_Ready = (current_state == INIT) || (current_state == IW);
  assign Read_data_Ready = (current_state == INIT) || (current_state == RDW);

  // -- Instruction Register Logic --
  always @(posedge clk) begin
    if (IRWrite) begin
      IR <= Instruction; // Reset instruction register
    end else begin
      IR <= IR;          // Fetch instruction from memory
    end
  end

  //============================================================================
  // PIPELINE STAGE 1: Instruction Fetch (IF)
  //============================================================================

  //-- PC Register --
  wire pc_write_enable = (current_state == IW && next_state == ID) ||                                          // Always update after IF (for PC+4 usually)
                        ((current_state == EX) && (is_J || is_jalr)) ||                               // Update for any jump in EX
                        ((current_state == EX) && is_B && branch_condition_satisfied); // Update for taken branch in EX
  pc instance_pc (
      .clk        (clk),
      .rst        (rst),
      .pc_write_enable (pc_write_enable), // Input: PC write enable signal (from control logic)
      .next_pc    (next_pc),              // Input: Next PC value (Calculated in EX stage)
      .pc         (current_pc)            // Output: Current PC value (Used across stages)
  );

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

  // -- Control Signals for Instruction Types --
  assign      is_I     = is_OPIMM || is_load || is_jalr; // I-type instruction
  assign      is_S     = (opcode == 7'b0100011);         // S-type instruction
  assign      is_B     = (opcode == 7'b1100011);         // B-type instruction
  assign      is_U     = is_lui || is_auipc;             // U-type instruction
  assign      is_J     = (opcode == 7'b1101111);         // J-type instruction
  assign      is_R     = (opcode == 7'b0110011);         // R-type instruction

  // -- Decode ALU and shifter operations based on instruction type --
  assign alu_src1 = (is_I || is_R || is_S || is_B) ? RF_rdata1  : // rs1 for most operations
                    (is_J)                         ? current_pc : // PC for JAL offset calculation
                    (is_lui)                       ? 32'b0      : // Zero for LUI (0 + imm)
                    (is_auipc)                     ? current_pc : // PC for AUIPC (PC + imm)
                                                     32'b0;       // Default to zero

  assign alu_src2 = (is_I || is_J) ? imm       : // Immediate for I-types (incl. JALR) and J-type (JAL)
                    (is_R)         ? RF_rdata2 : // rs2 for R-type operations
                    (is_S)         ? imm       : // Immediate for S-type (store address calculation)
                    (is_B)         ? RF_rdata2 : // rs2 for B-type (branch comparison)
                    (is_U)         ? imm       : // Immediate for U-type (LUI/AUIPC)
                                     32'b0;      // Default to zero

  assign shifter_src1 = RF_rdata1;                        // Source for shift operations is always rs1
  assign shifter_src2 = (is_R) ? RF_rdata2[4:0] :         // R-type shifts use lower 5 bits of rs2
                        (is_I) ? imm[4:0]       :         // I-type shifts use lower 5 bits of immediate (shamt)
                                 5'b0;                    // Default

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

  //-- Register File Read --
  reg_file instance_reg_file (
      .clk        (clk),
      .waddr      (RF_waddr),         // Input: Write address (From WB stage)
      .raddr1     (rs1),              // Input: Read address 1 (rs field from ID)
      .raddr2     (rs2),              // Input: Read address 2 (rt field from ID)
      .wen        (RF_wen),           // Input: Write enable (From WB stage)
      .wdata      (RF_wdata),         // Input: Write data (From WB stage)
      .rdata1     (RF_rdata1),        // Output: Read data 1 (rs value) -> To EX
      .rdata2     (RF_rdata2)         // Output: Read data 2 (rt value) -> To EX/MEM/WB
  );

  //============================================================================
  // PIPELINE STAGE 3: Execute (EX)
  //============================================================================

  //-- ALU Execution --
  wire [31:0] alu_out;                // ALU computation result

  alu instance_alu (
      .A          (alu_src1),         // Input A from Src Sel
      .B          (alu_src2),         // Input B from Src Sel
      .ALUop      (alu_op),           // Input Opcode from Op Gen
      .Overflow   (),
      .CarryOut   (),
      .Zero       (alu_zero),         // Output: Zero flag -> To EX (PC Ctrl), WB
      .Result     (alu_out)           // Output: ALU computation result -> To EX (PC Ctrl), MEM, WB
  );

  always @(posedge clk) begin
      alu_result <= alu_out;          // Store ALU result for MEM stage
  end

  //-- Shifter Execution --
  wire [31:0] shifter_out;                // Shifter computation result

  shifter instance_shifter (
      .A          (shifter_src1),         // Input Data from Src Sel
      .B          (shifter_src2),         // Input Shift Amount from Src Sel
      .Shiftop    (shifter_op),           // Input Opcode from ID
      .Result     (shifter_out)           // Output: Shifter result -> To WB
  );

  always @(posedge clk) begin
      shift_result <= shifter_out;        // Store Shifter result for WB stage
  end

  // Branch Target Address Calculation
  wire [31:0] branch_target = current_pc + imm_B - 4;

  // Branch Condition Satisfied Logic
  assign branch_condition_satisfied = (current_state == EX) ?
                                      (is_B ?
                                      // Check funct3 to determine the specific branch condition
                                      ( (funct3 == 3'b000) ? alu_zero                 : // BEQ: branch if (rs1 == rs2) -> Zero flag is set by (rs1 - rs2)
                                        (funct3 == 3'b001) ? !alu_zero                : // BNE: branch if (rs1 != rs2) -> Zero flag is not set
                                        (funct3 == 3'b100) ? alu_result[0]            : // BLT: branch if (rs1 < rs2) signed -> SLT result is 1
                                        (funct3 == 3'b101) ? !alu_result[0]           : // BGE: branch if (rs1 >= rs2) signed -> SLT result is 0
                                        (funct3 == 3'b110) ? alu_result[0]            : // BLTU: branch if (rs1 < rs2) unsigned -> SLTU result is 1
                                        (funct3 == 3'b111) ? !alu_result[0]           : // BGEU: branch if (rs1 >= rs2) unsigned -> SLTU result is 0
                                                             1'b0                    // Default: Should not happen for valid B-type funct3
                                      ) :
                                      1'b0) :
                                      1'b0; // Default: Not a B-type instruction, so condition is not satisfied.

  // Jump Target Address Calculation
  wire [31:0] jump_target = (is_J)    ? alu_result - 4                    :
                            (is_jalr) ? ((alu_result) & 32'hFFFFFFFE) : // JALR: Align to 2-byte boundary
                            32'b0;                                    // Default: Not a jump instruction, so target is not calculated.
  // -- PC Update Logic --
  assign      next_pc     = ((is_J || is_jalr) && current_state == EX) ? jump_target :         // Use jump target for JAL/JALR
                            (is_B && branch_condition_satisfied) ? branch_target : // Use branch target if condition is satisfied
                            current_pc + 4;                           // Default: PC + 4 for normal instruction flow

  // -- PC Store Logic --
  wire [31:0] pc_store;
  assign      pc_store    = (is_J || is_jalr) ? current_pc :      // Store PC+4 for JAL/JALR
                            32'b0;                                    // Default: Not a J or JALR instruction, so no PC store



  //============================================================================
  // PIPELINE STAGE 4: Memory Access (MEM)
  //============================================================================

  assign      Address     = (is_load || is_S) ? alu_result : 32'b0;   // Address for load/store operations
  wire [ 1:0] addr_offset = Address[1:0];                             // Address offset for load/store operations
  wire        addr_0      = (addr_offset == 2'b00);
  wire        addr_1      = (addr_offset == 2'b01);
  wire        addr_2      = (addr_offset == 2'b10);
  wire        addr_3      = (addr_offset == 2'b11);
  wire        funct3_SB   = (funct3 == 3'b000);
  wire        funct3_SH   = (funct3 == 3'b001);
  wire        funct3_SW   = (funct3 == 3'b010);
  wire        funct3_LB   = (funct3 == 3'b000);
  wire        funct3_LH   = (funct3 == 3'b001);
  wire        funct3_LW   = (funct3 == 3'b010);
  wire        funct3_LBU  = (funct3 == 3'b100);
  wire        funct3_LHU  = (funct3 == 3'b101);
  wire        mem_write_internal = (current_state == ST) && is_S;
  wire        mem_read_internal  = (current_state == LD) && is_load;

  // Memory Write Strobe Generation (Uses ID signals, EX result offset)
  assign      Write_strb  = {4{mem_write_internal}} & ( // Use is_store (mem_write_internal) from ID
                              (({4{funct3_SB}} & ((addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0010 : 0) | (addr_2 ? 4'b0100 : 0) | (addr_3 ? 4'b1000 : 0))) | // SB
                              ({4{funct3_SH}} & ((addr_0 ? 4'b0011 : 0) | (addr_2 ? 4'b1100 : 0))) |                                                    // SH
                              ({4{funct3_SW}} & (addr_0 ? 4'b1111 : 4'b0000))                                                                           // SW
                             )); // -> To Memory Interface

  assign      Write_data  = {32{mem_write_internal}} & ( // Format RF_rdata2 for stores -> To Memory Interface
                              (({32{funct3_SB}} & {4{RF_rdata2[7:0]}}) | // SB
                              ({32{funct3_SH}} & {2{RF_rdata2[15:0]}}) | // SH
                              ({32{funct3_SW}} & RF_rdata2)              // SW
                            ));

  assign      load_data          = (current_state == RDW && next_state == WB) ? // Process Read_data -> To WB Stage
                                    ( (funct3_LB || funct3_LBU) ?  // LB/LBU
                                      (addr_0 ? {{24{(~funct3[2] & Read_data [ 7])}}, Read_data [ 7: 0]} :
                                       addr_1 ? {{24{(~funct3[2] & Read_data [15])}}, Read_data [15: 8]} :
                                       addr_2 ? {{24{(~funct3[2] & Read_data [23])}}, Read_data [23:16]} :
                                                {{24{(~funct3[2] & Read_data [31])}}, Read_data [31:24]} )

                                    : (funct3_LH || funct3_LHU) ?  // LH/LHU
                                      (addr_0 ? {{16{(~funct3[2] & Read_data [15])}}, Read_data [15: 0]} :
                                       addr_2 ? {{16{(~funct3[2] & Read_data [31])}}, Read_data [31:16]} :
                                                32'b0 )

                                    : (funct3_LW) ? Read_data // LW

                                    : 32'b0 ) // Default unknown load
                                    : 32'b0;  // Default if not a load

  //============================================================================
  // PIPELINE STAGE 5: Write Back (WB)
  //============================================================================

  // -- Register Write Address and Enable Logic --
  assign      RF_waddr           = rd;
  assign      RF_wen             = Regwrite_fsm && (is_I || is_R || is_J || is_U) && (rd != 0);

  //-- Write Back Data Selection (Uses ID signals, EX results, MEM results) --
  wire [31:0] _RF_wdata;                                                       // Write data to RegFile (processed from ID, EX, MEM)
  assign      _RF_wdata          = (current_state == RDW && next_state == WB)  ? load_data    : // P1: load data from MEM
                                   (is_J || is_jalr)                           ? pc_store     : // P2: PC+4 for JAL/JALR
                                   (is_U)                                      ? alu_result   : // P3: Result from ALU for LUI/AUIPC
                                   ((is_R || is_I) && is_alu_operation)        ? alu_result   : // P4: Result from ALU for R-type/I-type
                                   ((is_R || is_I) && is_shifter_operation)    ? shift_result : // P5: Shifter result from EX
                                   32'b0;                                      // Default: 0 (No writeback)
                                                                               // -> To RegFile instance
  always @(posedge clk) begin
      RF_wdata <= _RF_wdata;                                                   // Store write data for RegFile
  end

  //----------------------------------------------------------------------------
  // Top-Level Output Assignments
  //----------------------------------------------------------------------------

  assign      PC                 = current_pc;                      // Output current PC (from IF stage)
  assign      MemWrite           = mem_write_internal;              // Output MemWrite signal (from ID stage control)
  assign      MemRead            = mem_read_internal;               // Output MemRead signal (from ID stage control)

//----------------------------------------------------------------------------
// Performance Counter Increment Signals (RISC-V Version)
//----------------------------------------------------------------------------
  reg [31:0] perf_cycle_count;             // cnt_0
  reg [31:0] perf_retired_inst_count;      // cnt_1
  reg [31:0] perf_retired_load_count;      // cnt_2
  reg [31:0] perf_retired_store_count;     // cnt_3
  reg [31:0] perf_branch_executed_count;   // cnt_4
  reg [31:0] perf_branch_taken_count;      // cnt_5
  reg [31:0] perf_if_stall_count;          // cnt_6
  reg [31:0] perf_mem_access_stall_count;  // cnt_7 (LD/ST stalls on Mem_Req_Ready)
  reg [31:0] perf_iw_stall_count;          // cnt_8
  reg [31:0] perf_rdw_stall_count;         // cnt_9
  reg [31:0] perf_jump_executed_count;     // cnt_10
  reg [31:0] perf_alu_op_executed_count;   // cnt_11
  reg [31:0] perf_shift_op_executed_count; // cnt_12
  reg [31:0] perf_nop_in_id_count;         // cnt_13
  reg [31:0] perf_total_mem_ops_count;     // cnt_14
  reg [31:0] perf_reg_writes_count;        // cnt_15


  // Logic for incrementing counters
  wire increment_retired_inst;
  wire increment_retired_load;
  wire increment_retired_store;
  wire increment_branch_executed;
  wire increment_branch_taken;
  wire increment_if_stall;
  wire increment_mem_access_stall;
  wire increment_iw_stall;
  wire increment_rdw_stall;
  wire increment_jump_executed;
  wire increment_alu_op_executed;
  wire increment_shift_op_executed;
  wire increment_nop_in_id;
  wire increment_total_mem_ops;
  wire increment_reg_writes;

  wire is_nop = (IR == 32'h00000013); // ADDI x0, x0, 0, decoded from IR
  assign increment_retired_inst =
      ( (current_state == WB && RF_wen && !is_nop) && (is_R || is_OPIMM || is_U || is_J || is_jalr) ) || // ALU/Shift/U-type/Jumps writing to rd
      ( (current_state == WB && RF_wen && !is_nop) && is_load ) ||                                      // Loads writing to rd
      ( (current_state == ST && Mem_Req_Ready && !is_nop) && is_S ) ||                                  // Stores accepted by memory
      ( (current_state == EX && !is_nop) && (is_B || is_ebreak) && (next_state == IF) );                // Branches or EBREAK completing EX
  assign increment_retired_load      = (current_state == WB && RF_wen && !is_nop && is_load);
  assign increment_retired_store     = (current_state == ST && Mem_Req_Ready && !is_nop && is_S);
  assign increment_branch_executed   = (current_state == EX && !is_nop && is_B);
  assign increment_branch_taken      = (current_state == EX && !is_nop && is_B && branch_condition_satisfied);
  assign increment_if_stall          = (current_state == IF && !Inst_Req_Ready && !rst);
  assign increment_mem_access_stall  = ((current_state == LD || current_state == ST) && !Mem_Req_Ready && !rst);
  assign increment_iw_stall          = (current_state == IW && !Inst_Valid && !rst);
  assign increment_rdw_stall         = (current_state == RDW && !Read_data_Valid && !rst);
  assign increment_jump_executed     = (current_state == EX && !is_nop && (is_J || is_jalr));
  assign increment_alu_op_executed   = (current_state == EX && !is_nop &&
                                      (is_R || is_OPIMM) && is_alu_operation);
  assign increment_shift_op_executed = (current_state == EX && !is_nop &&
                                        (is_R || is_OPIMM) && is_shifter_operation);
  assign increment_nop_in_id         = (current_state == ID && is_nop && !rst);
  assign increment_total_mem_ops     = (current_state == EX && !is_nop && (is_load || is_S));
  assign increment_reg_writes        = (current_state == WB && RF_wen && !rst);

  // cnt_0: Cycle Count
  always @(posedge clk) begin
    if (rst) begin
      perf_cycle_count <= 32'd0;
    end else begin
      perf_cycle_count <= perf_cycle_count + 1;
    end
  end
  assign cpu_perf_cnt_0 = perf_cycle_count;

  // cnt_1: Retired Instruction Count
  always @(posedge clk) begin
    if (rst) begin
      perf_retired_inst_count <= 32'd0;
    end else if (increment_retired_inst) begin
      perf_retired_inst_count <= perf_retired_inst_count + 1;
    end
  end
  assign cpu_perf_cnt_1 = perf_retired_inst_count;

  // cnt_2: Retired Load Instruction Count
  always @(posedge clk) begin
    if (rst) begin
      perf_retired_load_count <= 32'd0;
    end else if (increment_retired_load) begin
      perf_retired_load_count <= perf_retired_load_count + 1;
    end
  end
  assign cpu_perf_cnt_2 = perf_retired_load_count;

  // cnt_3: Retired Store Instruction Count
  always @(posedge clk) begin
    if (rst) begin
      perf_retired_store_count <= 32'd0;
    end else if (increment_retired_store) begin
      perf_retired_store_count <= perf_retired_store_count + 1;
    end
  end
  assign cpu_perf_cnt_3 = perf_retired_store_count;

  // cnt_4: Total Branch Instructions Executed
  always @(posedge clk) begin
    if (rst) begin
      perf_branch_executed_count <= 32'd0;
    end else if (increment_branch_executed) begin
      perf_branch_executed_count <= perf_branch_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_4 = perf_branch_executed_count;

  // cnt_5: Taken Branch Instructions Executed
  always @(posedge clk) begin
    if (rst) begin
      perf_branch_taken_count <= 32'd0;
    end else if (increment_branch_taken) begin
      perf_branch_taken_count <= perf_branch_taken_count + 1;
    end
  end
  assign cpu_perf_cnt_5 = perf_branch_taken_count;

  // cnt_6: IF Stage Stalls
  always @(posedge clk) begin
    if (rst) begin
      perf_if_stall_count <= 32'd0;
    end else if (increment_if_stall) begin
      perf_if_stall_count <= perf_if_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_6 = perf_if_stall_count;

  // cnt_7: Data Memory Access Stalls (LD/ST stalls on Mem_Req_Ready)
  always @(posedge clk) begin
    if (rst) begin
      perf_mem_access_stall_count <= 32'd0;
    end else if (increment_mem_access_stall) begin
      perf_mem_access_stall_count <= perf_mem_access_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_7 = perf_mem_access_stall_count;

  // cnt_8: IW Stage Stalls
  always @(posedge clk) begin
    if (rst) begin
      perf_iw_stall_count <= 32'd0;
    end else if (increment_iw_stall) begin
      perf_iw_stall_count <= perf_iw_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_8 = perf_iw_stall_count;

  // cnt_9: RDW Stage Stalls
  always @(posedge clk) begin
    if (rst) begin
      perf_rdw_stall_count <= 32'd0;
    end else if (increment_rdw_stall) begin
      perf_rdw_stall_count <= perf_rdw_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_9 = perf_rdw_stall_count;

  // cnt_10: Jump Instructions Executed
  always @(posedge clk) begin
    if (rst) begin
      perf_jump_executed_count <= 32'd0;
    end else if (increment_jump_executed) begin
      perf_jump_executed_count <= perf_jump_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_10 = perf_jump_executed_count;

  // cnt_11: ALU Instructions Executed
  always @(posedge clk) begin
    if (rst) begin
      perf_alu_op_executed_count <= 32'd0;
    end else if (increment_alu_op_executed) begin
      perf_alu_op_executed_count <= perf_alu_op_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_11 = perf_alu_op_executed_count;

  // cnt_12: Shift Instructions Executed
  always @(posedge clk) begin
    if (rst) begin
      perf_shift_op_executed_count <= 32'd0;
    end else if (increment_shift_op_executed) begin
      perf_shift_op_executed_count <= perf_shift_op_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_12 = perf_shift_op_executed_count;

  // cnt_13: NOP Instructions Encountered in ID
  always @(posedge clk) begin
    if (rst) begin
      perf_nop_in_id_count <= 32'd0;
    end else if (increment_nop_in_id) begin
      perf_nop_in_id_count <= perf_nop_in_id_count + 1;
    end
  end
  assign cpu_perf_cnt_13 = perf_nop_in_id_count;

  // cnt_14: Total Memory Operations (Load + Store issued to EX)
  always @(posedge clk) begin
    if (rst) begin
      perf_total_mem_ops_count <= 32'd0;
    end else if (increment_total_mem_ops) begin
      perf_total_mem_ops_count <= perf_total_mem_ops_count + 1;
    end
  end
  assign cpu_perf_cnt_14 = perf_total_mem_ops_count;

  // cnt_15: Register File Writes
  always @(posedge clk) begin
    if (rst) begin
      perf_reg_writes_count <= 32'd0;
    end else if (increment_reg_writes) begin
      perf_reg_writes_count <= perf_reg_writes_count + 1;
    end
  end
  assign cpu_perf_cnt_15 = perf_reg_writes_count;

endmodule

//==============================================================================
// Module: pc
// Description: Program Counter register. Stores the address of the next
//              instruction to be fetched.
//==============================================================================
module pc (
    input         clk,
    input         rst,
    input         pc_write_enable,
    input  [31:0] next_pc,
    output reg [31:0] pc
);
  always @(posedge clk) begin
    if (rst) begin
      pc <= 32'h00000000;
    end else if (pc_write_enable) begin
      pc <= next_pc;
    end
  end
endmodule
