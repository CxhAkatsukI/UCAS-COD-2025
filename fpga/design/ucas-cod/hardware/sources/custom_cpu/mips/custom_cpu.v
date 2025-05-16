// timescale directive: simulation time unit is 10ns, precision is 1ns
`timescale 10ns / 1ns

// Macro definitions for bus widths
`define ADDR_WIDTH 5  // Register file address width
`define DATA_WIDTH 32 // Data bus width

//==============================================================================
// Module: custom_cpu
// Description: A simple MIPS-like CPU core with integrated control logic.
//              (Code organized by strict pipeline stage definitions)
//==============================================================================
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
  // Internal Wires - Connecting Logic Blocks and Modules
  // (Grouped here for clarity, used across stages)
  //----------------------------------------------------------------------------

  //-- Signals generated in ID (purely from Instruction) --
  wire [ 5:0] opcode;               // Opcode field
  wire [ 4:0] rs;                   // Source register 1 specifier
  wire [ 4:0] rt;                   // Source register 2 specifier / Branch Func
  wire [ 4:0] rd;                   // Destination register specifier (R-type)
  wire [ 4:0] shamt;                // Shift amount (R-type shift)
  wire [ 5:0] funct;                // Function field (R-type)
  wire [15:0] imm_16;               // 16-bit immediate value
  wire [25:0] imm_J;                // 26-bit immediate for jump
  wire [31:0] imm_SE;               // Sign-extended immediate
  wire [31:0] imm_0E;               // Zero-extended immediate
  wire [31:0] imm_B_ext;            // Sign-extended branch immediate
  wire [31:0] lui_result;           // Result for LUI instruction
  wire        use_zero_extend;      // Control for immediate extension type
  reg  [ 8:0] current_state;        // Current state of the FSM
  reg  [ 8:0] next_state;           // Next state of the FSM
  reg  [31:0] IR;                   // Instruction Register (holds current instruction)

  wire        reg_dst_input;          // Selects destination register (rd/rt/ra hint)
  wire        is_branch;              // Indicates Branch instruction
  wire        branch_condition_satisfied; // Indicates branch condition is satisfied
  wire        mem_read_internal;      // Internal Memory read enable (Load)
  wire        mem_write_internal;     // Internal Memory write enable (Store)
  wire        alu_src_imm_input;      // Selects ALU source 2 (Reg/Imm)
  wire        reg_write_cond;         // Precondition for register write enable (base check)
  wire        alu_op_ok;              // Indicates ALUOp can be derived from opcode
  wire [ 2:0] alu_op_cond;            // ALU operation hint from opcode
  wire        is_alu_operation;       // Indicates an ALU operation is needed
  wire        is_shift_operation;     // Indicates a Shift operation is needed
  wire [ 2:0] alu_op;                 // Decoded ALU operation (R/I type)
  wire [ 1:0] shifter_op;             // Decoded Shift operation type
  wire        is_shamt;               // Indicates shamt is used for shift amount
  wire        is_zero_cmp;            // Indicates branch compares rs against zero
  wire        is_move;                // Indicates MOVZ/MOVN
  wire        is_lui;                 // Indicates LUI instruction
  wire        is_load;                // Indicates Load instruction
  wire        is_store;               // Indicates Store instruction
  wire        is_load_store;          // Indicates Load/Store instruction
  wire [ 2:0] move_alu_op;            // ALU operation code for MOVZ/MOVN
  wire        is_jump;                // Indicates any Jump instruction occurred (J, JAL, JR, JALR)
  wire        is_link_jump;           // Indicates JAL or JALR instruction
  wire        is_j_instr;
  wire        is_jal_instr;
  wire        is_jr_instr;
  wire        is_jalr_instr;
  wire        is_REGIMM;
  wire        NOP;                    // Indicates NOP instruction (all bits 0)
  wire        write_disallowed;       // Instr. type that never writes back
  wire        intermediate_reg_write_cond; // Base write condition refined

  //-- Signals from Register File (ID Stage Read) --
  wire [31:0] RF_rdata1;              // Data read from RegFile port 1 (rs)
  wire [31:0] RF_rdata2;              // Data read from RegFile port 2 (rt)

  //-- Signals from/for PC Path (Generated/Used across stages) --
  wire [31:0] next_pc;                // Next program counter value (Calculated in EX)
  wire [31:0] current_pc;             // Current program counter value (from PC module in IF)
  wire [31:0] pc_store;               // PC+8 for JAL/JALR link address (Calculated in EX)

  //-- Signals from ALU/Shifter Path (Generated in EX) --
  wire [31:0] alu_src1;               // First ALU operand
  wire [31:0] alu_src2;               // Second ALU operand
  wire [31:0] shifter_src1;           // First Shifter operand (data)
  wire [31:0] shifter_src2;           // Second Shifter operand (shift amount)
  wire [ 2:0] alu_op_final;           // Final ALU operation control to ALU
  wire        alu_zero;               // ALU Zero flag
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
            if (NOP) begin
              next_state = IF;
            end
            else begin
              next_state = EX;
            end
      end
      EX : begin
        if (is_j_instr || is_REGIMM || is_branch) begin
          next_state = IF;
        end
        else if (is_load_store) begin
          if (is_load) begin
            next_state = LD;
          end
          else if (is_store) begin
            next_state = ST;
          end
          else begin
            next_state = IF;
          end
        end
        else begin
          next_state = WB;
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
                       ((current_state == EX) && is_jump) ||                               // Update for any jump in EX
                       ((current_state == EX) && is_branch && branch_condition_satisfied); // Update for taken branch in EX
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

  //-- Instruction Field Decoding --
  assign      opcode   = IR[31:26]; // Opcode field
  assign      rs       = IR[25:21]; // Source register 1 specifier
  assign      rt       = IR[20:16]; // Source register 2 specifier / Branch Func
  assign      rd       = IR[15:11]; // Destination register specifier (R-type)
  assign      shamt    = IR[10: 6]; // Shift amount (R-type shift)
  assign      funct    = IR[ 5: 0]; // Function field (R-type)
  assign      imm_16   = IR[15: 0]; // 16-bit immediate value
  assign      imm_J    = IR[25: 0]; // 26-bit immediate for jump

  //-- Immediate Value Processing (Purely from Instruction) --
  assign      NOP      = (~|IR);                                      // NOP instruction (all bits 0)
  assign      imm_SE   = {{16{imm_16[15]}}, imm_16};                  // Sign-extended immediate
  assign      imm_0E   = {16'b0, imm_16};                             // Zero-extended immediate
  assign      imm_B_ext= {{16{imm_16[15]}}, imm_16};                  // Sign-extended branch immediate (used in EX)
  assign      lui_result = {imm_16, 16'b0};                           // Result for LUI instruction (used in WB)
  assign      use_zero_extend = (opcode[5:3] == 3'b001) && opcode[2]; // Use Zero Ext for ANDI/ORI/XORI (used in EX)

  //-- Primary Control Signal Generation (Purely from Instruction) --
  wire        is_branch_sub     = (opcode[5:2] == 4'b0001);                    // Specific branch types
  wire        is_branch_slt     = (opcode == 6'b000001);                       // Branches that use slt as alu_op
  assign      is_branch         = (is_branch_sub || is_branch_slt);            // General branch flag
  assign      reg_dst_input     = opcode[5] ^ opcode[3];                       // Hint for WB Stage dest reg sel
  assign      mem_read_internal = (current_state == LD) && (opcode[5:3] == 3'b100); // Control for MEM Stage
  assign      mem_write_internal= (current_state == ST) && (opcode[5:3] == 3'b101); // Control for MEM Stage
  assign      alu_src_imm_input = ((opcode[5] || opcode[3]) && !opcode[4]);    // Control for EX Stage (ALU Src Sel)

  //-- Secondary Control Signal Generation (Purely from Instruction or derived ID signals) --
  wire        imm_arithmetic    = (opcode[5:3] == 3'b001 && ~&opcode[2:0]);       // I-type Arith?
  assign      is_load           = opcode[5:3] == 3'b100;                          // Load?
  assign      is_store          = opcode[5:3] == 3'b101;                          // Store?
  assign      is_load_store     = opcode[5:3] == 3'b100 || opcode[5:3] == 3'b101; // Load or Store?
  assign      reg_write_cond    = !mem_write_internal && !is_branch;              // Base RegWrite condition (used in WB)

  // -- Decode I-type arith op based on opcode --
  wire [ 2:0] arith_type;
  assign      arith_type[0]     = (~opcode[2] & opcode[1]) | (opcode[2] & opcode[0]);
  assign      arith_type[1]     = ~opcode[2];
  assign      arith_type[2]     = opcode[1] & ~opcode[0];
  assign      alu_op_cond       = is_branch_slt  ? 3'b111 :
                                  is_branch_sub  ? 3'b110 :
                                  is_load_store  ? 3'b010 :
                                  imm_arithmetic ? arith_type :
                                  3'bxxx;
  assign      alu_op_ok         = (imm_arithmetic || is_branch || is_load_store);      // Validity of hint for EX

  assign      is_alu_operation   = ((~|opcode && funct[5] == 1'b1) || imm_arithmetic); // Is it an ALU op? (Used EX/WB)
  assign      is_shift_operation = (~|opcode && ~|funct[5:3]);                         // Is it a Shift op? (Used EX/WB)

  // -- Decode R-type arith op based on funct --
  wire [ 2:0] r_type_arith_op;
  assign      r_type_arith_op[0] = (funct[3] & funct[1]) | (~funct[3] & funct[2] & funct[0]);
  assign      r_type_arith_op[1] = funct[3] | ~funct[2];
  assign      r_type_arith_op[2] = (funct[3] & ~funct[0]) | (~funct[3] & funct[1]);
  assign      alu_op             = (~|opcode) ? r_type_arith_op : alu_op_cond ;        // Base ALU op (R/I type) (Used EX)

  // -- Decode R-type shift op based on funct --
  wire [ 1:0] shift_type;                                                              // Decode R-type shift op based on funct
  assign      shift_type[0]      = funct[1] & funct[0];
  assign      shift_type[1]      = funct[1];
  assign      shifter_op         = is_shift_operation ? shift_type : 2'b00;            // Shift op type (Used EX)
  assign      is_shamt           = is_shift_operation && ~funct[2];                    // Use shamt? (Used EX)

  assign      is_zero_cmp        = is_branch && (opcode[2:0] == 3'b110 || opcode[2:0] == 3'b111 || opcode[2:0] == 3'b001); // Compare rs to 0? (Used EX)

  assign      is_move            = (~|opcode && funct[1] && funct[3] && !funct[5]);    // MOVZ/MOVN? (Used EX/WB)
  assign      is_lui             = (opcode == 6'b001111);                              // LUI? (Used WB)
  assign      move_alu_op        = 3'b001;                                             // ALU Op for Move (Used EX)

  assign      is_j_instr         = (opcode == 6'b000010);
  assign      is_jal_instr       = (opcode == 6'b000011);
  assign      is_jr_instr        = (~|opcode && funct == 6'b001000);
  assign      is_jalr_instr      = (~|opcode && funct == 6'b001001);
  assign      is_jump            = is_j_instr || is_jal_instr || is_jr_instr || is_jalr_instr; // Is it any Jump? (Used EX)
  assign      is_link_jump       = is_jal_instr || is_jalr_instr;                              // Is it JAL/JALR? (Used EX/WB)
  assign      is_REGIMM          = (opcode == 6'b000001);                                      // Is it REGIMM? (Used EX)

  assign      write_disallowed   = is_j_instr || is_jr_instr || mem_write_internal;            // Instr. that don't write back (refined) (Used WB)
  assign      intermediate_reg_write_cond = reg_write_cond && !write_disallowed;               // Base write condition refined (Used WB)




  //-- Register File Read --
  reg_file instance_reg_file (
      .clk        (clk),
      .waddr      (RF_waddr),         // Input: Write address (From WB stage)
      .raddr1     (rs),               // Input: Read address 1 (rs field from ID)
      .raddr2     (rt),               // Input: Read address 2 (rt field from ID)
      .wen        (RF_wen),           // Input: Write enable (From WB stage)
      .wdata      (RF_wdata),         // Input: Write data (From WB stage)
      .rdata1     (RF_rdata1),        // Output: Read data 1 (rs value) -> To EX
      .rdata2     (RF_rdata2)         // Output: Read data 2 (rt value) -> To EX/MEM/WB
  );

  //============================================================================
  // PIPELINE STAGE 3: Execute (EX)
  //============================================================================

  //-- ALU Source Selector Logic (Uses ID signals, Reg Data) --
  assign      alu_src1           = (is_move) ? 32'b0 : RF_rdata1;                         // ALU Input A
  assign      alu_src2           = (is_zero_cmp)       ? 32'b0 :                          // ALU Input B
                                   (alu_src_imm_input) ? (use_zero_extend ? imm_0E : imm_SE) :
                                   RF_rdata2;

  //-- Shifter Source Selector Logic (Uses ID signals, Reg Data) --
  assign      shifter_src1       = RF_rdata2;                                             // Shifter Input A (Data)
  assign      shifter_src2       = (is_shamt) ? {27'b0, shamt} : {27'b0, RF_rdata1[4:0]}; // Shifter Input B (Amount)

  //-- ALU Op Generator Logic (Uses ID signals) --
  assign      alu_op_final       = (is_move)          ? move_alu_op :
                                   (is_alu_operation) ? alu_op :
                                   (alu_op_ok)        ? alu_op_cond :
                                   3'b010;                                                // Final ALU Op -> To ALU

  //-- ALU Execution --
  wire [31:0] alu_out;                // ALU computation result

  alu instance_alu (
      .A          (alu_src1),         // Input A from Src Sel
      .B          (alu_src2),         // Input B from Src Sel
      .ALUop      (alu_op_final),     // Input Opcode from Op Gen
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
      .B          (shifter_src2[4:0]),    // Input Shift Amount from Src Sel
      .Shiftop    (shifter_op),           // Input Opcode from ID
      .Result     (shifter_out)           // Output: Shifter result -> To WB
  );

  always @(posedge clk) begin
      shift_result <= shifter_out;        // Store Shifter result for WB stage
  end

  //-- PC Controller Logic (Uses ID signals, EX results, IF PC) --
  assign      branch_condition_satisfied = is_branch &&                                                                    // Check using signals from ID and results from EX
                                           ( (is_branch_slt && (rt[0] ^ alu_result[0])) ||                                 // REGIMM check using rt(funct_branch) from ID, alu_result from EX
                                             (is_branch_sub && opcode[1] && (opcode[0] ^ (alu_result[31] || alu_zero))) || // BLEZ/BGTZ check using opcode from ID, alu_result/zero from EX
                                             (is_branch_sub && !opcode[1] && (opcode[0] ^ alu_zero))                       // BEQ/BNE check using opcode from ID, alu_zero from EX
                                           );

  wire [31:0] branch_target      = (current_pc) + (imm_B_ext << 2);                                                   // Branch target addr calculation

  wire [31:0] jump_target        = (is_j_instr || is_jal_instr) ? {current_pc[31:28], imm_J, 2'b00} : RF_rdata1;      // J/JAL or JR/JALR target calculation

  // Next PC Selection based on control signals (ID) and conditions (EX)
  assign      next_pc            = (rst)                                                    ? 32'h00000000 :          // Reset PC value
                                   (current_state == EX && is_jump)                         ? jump_target  :          // Jump target selection
                                   (current_state == EX && is_branch && branch_condition_satisfied) ? branch_target : // Branch target selection
                                   current_pc + 4;                                                                    // Default: PC + 4 -> To IF

  // PC+8 Calculation for Link Instructions (Uses ID signal, IF PC)
  assign      pc_store           = is_link_jump ? (current_pc + 4) : 32'b0;                                           // Value to store for JAL/JALR -> To WB

  //============================================================================
  // PIPELINE STAGE 4: Memory Access (MEM)
  //============================================================================

  //-- Load/Store Address and Data Logic (Uses ID signals, EX results, ID reg data) --
  wire [ 1:0] addr_offset        = alu_result[1:0];            // Byte offset (from EX result)
  wire        addr_0             = (addr_offset == 2'b00);
  wire        addr_1             = (addr_offset == 2'b01);
  wire        addr_2             = (addr_offset == 2'b10);
  wire        addr_3             = (addr_offset == 2'b11);

  // Memory Address Output Calculation (Uses EX result)
  assign      Address            = {alu_result[31:2], 2'b00};  // Word-aligned address -> To Memory Interface

  // Memory Write Strobe Generation (Uses ID signals, EX result offset)
  assign      Write_strb         = {4{mem_write_internal}} & ( // Use is_store (mem_write_internal) from ID
                                     (({4{opcode[1:0] == 2'b00}} & ((addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0010 : 0) | (addr_2 ? 4'b0100 : 0) | (addr_3 ? 4'b1000 : 0))) | // SB
                                     ({4{opcode[1:0] == 2'b01}} & ((addr_0 ? 4'b0011 : 0) | (addr_2 ? 4'b1100 : 0))) |                                                    // SH
                                     ({4{opcode[1:0] == 2'b11}} & (addr_0 ? 4'b1111 : 4'b0000)) |                                                                         // SW
                                     ({4{opcode[2:0] == 3'b010}} & ((addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0011 : 0) | (addr_2 ? 4'b0111 : 0) | (addr_3 ? 4'b1111 : 0))) | // SWL
                                     ({4{opcode[2:0] == 3'b110}} & ((addr_0 ? 4'b1111 : 0) | (addr_1 ? 4'b1110 : 0) | (addr_2 ? 4'b1100 : 0) | (addr_3 ? 4'b1000 : 0)))   // SWR
                                    )); // -> To Memory Interface

  assign      Write_data         = {32{mem_write_internal}} & ( // Format RF_rdata2 for stores -> To Memory Interface
                                     (({32{opcode[1:0] == 2'b00}} & {4{RF_rdata2[7:0]}}) | // SB
                                     ({32{opcode[1:0] == 2'b01}} & {2{RF_rdata2[15:0]}}) | // SH
                                     ({32{opcode[1:0] == 2'b11}} & RF_rdata2) |            // SW
                                     ({32{opcode[2:0] == 3'b010}} & ( // SWL (Logic kept as-is)
                                         (addr_0 ? {24'b0, RF_rdata2[31:24]} :
                                          addr_1 ? {16'b0, RF_rdata2[31:16]} :
                                          addr_2 ? { 8'b0, RF_rdata2[31: 8]} :
                                                   RF_rdata2)
                                     )) |
                                     ({32{opcode[2:0] == 3'b110}} & ( // SWR (Logic kept as-is)
                                         (addr_0 ? RF_rdata2 :
                                          addr_1 ? {RF_rdata2[23:0],  8'b0} :
                                          addr_2 ? {RF_rdata2[15:0], 16'b0} :
                                                   {RF_rdata2[ 7:0], 24'b0})
                                     )))
                                   );

   // Processing of Data Read from Memory (Uses ID signals, EX result offset, ID reg data, Mem input)
   assign      load_data          = (current_state == RDW && next_state == WB) ? // Process Read_data -> To WB Stage
                                    ( (opcode[1:0] == 2'b00) ?  // LB/LBU
                                      (addr_0 ? {{24{(~opcode[2] & Read_data [ 7])}}, Read_data [ 7: 0]} :
                                       addr_1 ? {{24{(~opcode[2] & Read_data [15])}}, Read_data [15: 8]} :
                                       addr_2 ? {{24{(~opcode[2] & Read_data [23])}}, Read_data [23:16]} :
                                                {{24{(~opcode[2] & Read_data [31])}}, Read_data [31:24]} )

                                    : (opcode[1:0] == 2'b01) ?  // LH/LHU
                                      (addr_0 ? {{16{(~opcode[2] & Read_data [15])}}, Read_data [15: 0]} :
                                       addr_2 ? {{16{(~opcode[2] & Read_data [31])}}, Read_data [31:16]} :
                                                32'b0 )

                                    : (opcode[1:0] == 2'b11) ? Read_data // LW

                                    : (opcode[2:0] == 3'b010) ? // LWL
                                      (addr_0 ? {Read_data [ 7: 0], RF_rdata2 [23: 0]} :
                                       addr_1 ? {Read_data [15: 0], RF_rdata2 [15: 0]} :
                                       addr_2 ? {Read_data [23: 0], RF_rdata2 [ 7: 0]} :
                                                Read_data )

                                    : (opcode[2:0] == 3'b110) ? // LWR
                                      (addr_0 ? Read_data :
                                       addr_1 ? {RF_rdata2 [31:24], Read_data [31: 8]} :
                                       addr_2 ? {RF_rdata2 [31:16], Read_data [31:16]} :
                                                {RF_rdata2 [31: 8], Read_data [31:24]} )

                                    : 32'b0 ) // Default unknown load
                                    : 32'b0;  // Default if not a load


  //============================================================================
  // PIPELINE STAGE 5: Write Back (WB)
  //============================================================================

  //-- Register Write Address and Enable Logic (Uses ID signals, EX results) --
  assign      RF_waddr           = (is_link_jump) ? 5'd31 :           // JAL/JALR -> $ra (from ID)
                                   (reg_dst_input) ? rt :             // I-type/Load hint -> rt (from ID)
                                   rd;                                // R-type hint -> rd (from ID)
                                                                      // -> To RegFile instance

  assign      RF_wen             = Regwrite_fsm & ((intermediate_reg_write_cond && !is_move) || // Use conditions from ID and...
                                   (is_move && (funct[0] ^ alu_zero) && reg_write_cond));       // ...MOVZ/N check using alu_zero from EX
                                                                                                // -> To RegFile instance

  //-- Write Back Data Selection (Uses ID signals, EX results, MEM results) --
  wire [31:0] _RF_wdata;                                                       // Write data to RegFile (processed from ID, EX, MEM)
  assign      _RF_wdata          = (is_lui)             ? lui_result :         // P1: LUI (from ID)
                                   (current_state == RDW && next_state == WB)  ? load_data :          // P2: Load result from MEM
                                   (is_move)            ? RF_rdata1 :          // P3: MOVZ/MOVN result (rs) from ID
                                   (is_alu_operation)   ? alu_result :         // P4: Other ALU result from EX
                                   (is_shift_operation) ? shift_result :       // P5: Shifter result from EX
                                   (is_link_jump)       ? pc_store :           // P6: Link address (PC+8) from EX
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

  //============================================================================
  // Performance Counters
  //============================================================================

  reg [31:0] perf_cycle_count;
  reg [31:0] perf_retired_inst_count;
  reg [31:0] perf_retired_load_count;
  reg [31:0] perf_retired_store_count;
  reg [31:0] perf_branch_executed_count;
  reg [31:0] perf_branch_taken_count;
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


  // Determine when an instruction is considered retired (Same as before)
  assign increment_retired_inst =
        (current_state == WB && Regwrite_fsm && !NOP && (is_alu_operation || is_shift_operation || is_lui || is_link_jump)) ||
        (current_state == WB && Regwrite_fsm && !NOP && is_load) ||
        (current_state == ST && Mem_Req_Ready && !NOP && is_store) ||
        (current_state == EX && !NOP &&
            (is_j_instr || is_jr_instr || is_REGIMM || (is_branch && !is_link_jump)) &&
            (next_state == IF)
        );

  assign increment_retired_load = (current_state == WB && Regwrite_fsm && !NOP && is_load);
  assign increment_retired_store = (current_state == ST && Mem_Req_Ready && !NOP && is_store);
  assign increment_branch_executed = (current_state == EX && !NOP && is_branch);
  assign increment_branch_taken = (current_state == EX && !NOP && is_branch && branch_condition_satisfied);
  assign increment_if_stall = (current_state == IF && !Inst_Req_Ready && !rst);
  assign increment_mem_access_stall = ((current_state == LD || current_state == ST) && !Mem_Req_Ready && !rst);
  assign increment_iw_stall = (current_state == IW && !Inst_Valid && !rst);
  assign increment_rdw_stall = (current_state == RDW && !Read_data_Valid && !rst);
  assign increment_jump_executed = (current_state == EX && !NOP && is_jump);
  // For ALU/Shift, ensure it's not a mem op address calc or branch compare
  assign increment_alu_op_executed = (current_state == EX && !NOP && is_alu_operation && !is_load_store && !is_branch && !is_jump);
  assign increment_shift_op_executed = (current_state == EX && !NOP && is_shift_operation && !is_load_store && !is_branch && !is_jump);
  assign increment_nop_in_id = (current_state == ID && NOP && !rst); // NOP is decoded in ID
  assign increment_total_mem_ops = (current_state == EX && !NOP && is_load_store); // Count when it enters EX, destined for MEM
  assign increment_reg_writes = (current_state == WB && RF_wen && !rst);


  // Cycle Count (Same as before)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_cycle_count <= 32'd0;
    end else begin
      perf_cycle_count <= perf_cycle_count + 1;
    end
  end
  assign cpu_perf_cnt_0 = perf_cycle_count;

  // Retired Instruction Count (Same as before)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_retired_inst_count <= 32'd0;
    end else if (increment_retired_inst) begin
      perf_retired_inst_count <= perf_retired_inst_count + 1;
    end
  end
  assign cpu_perf_cnt_1 = perf_retired_inst_count;

  // Retired Load Instruction Count (Same as before)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_retired_load_count <= 32'd0;
    end else if (increment_retired_load) begin
      perf_retired_load_count <= perf_retired_load_count + 1;
    end
  end
  assign cpu_perf_cnt_2 = perf_retired_load_count;

  // Retired Store Instruction Count (Same as before)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_retired_store_count <= 32'd0;
    end else if (increment_retired_store) begin
      perf_retired_store_count <= perf_retired_store_count + 1;
    end
  end
  assign cpu_perf_cnt_3 = perf_retired_store_count;

  // Total Branch Instructions Executed (Same as before)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_branch_executed_count <= 32'd0;
    end else if (increment_branch_executed) begin
      perf_branch_executed_count <= perf_branch_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_4 = perf_branch_executed_count;

  // Taken Branch Instructions Executed (Same as before)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_branch_taken_count <= 32'd0;
    end else if (increment_branch_taken) begin
      perf_branch_taken_count <= perf_branch_taken_count + 1;
    end
  end
  assign cpu_perf_cnt_5 = perf_branch_taken_count;


  // ---- New Counter Implementations ----

  // cnt_6: IF Stage Stalls
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_if_stall_count <= 32'd0;
    end else if (increment_if_stall) begin
      perf_if_stall_count <= perf_if_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_6 = perf_if_stall_count;

  // cnt_7: Data Memory Access Stalls (LD/ST stalls on Mem_Req_Ready)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_mem_access_stall_count <= 32'd0;
    end else if (increment_mem_access_stall) begin
      perf_mem_access_stall_count <= perf_mem_access_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_7 = perf_mem_access_stall_count;

  // cnt_8: IW Stage Stalls
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_iw_stall_count <= 32'd0;
    end else if (increment_iw_stall) begin
      perf_iw_stall_count <= perf_iw_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_8 = perf_iw_stall_count;

  // cnt_9: RDW Stage Stalls
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_rdw_stall_count <= 32'd0;
    end else if (increment_rdw_stall) begin
      perf_rdw_stall_count <= perf_rdw_stall_count + 1;
    end
  end
  assign cpu_perf_cnt_9 = perf_rdw_stall_count;

  // cnt_10: Jump Instructions Executed
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_jump_executed_count <= 32'd0;
    end else if (increment_jump_executed) begin
      perf_jump_executed_count <= perf_jump_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_10 = perf_jump_executed_count;

  // cnt_11: ALU Instructions Executed
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_alu_op_executed_count <= 32'd0;
    end else if (increment_alu_op_executed) begin
      perf_alu_op_executed_count <= perf_alu_op_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_11 = perf_alu_op_executed_count;

  // cnt_12: Shift Instructions Executed
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_shift_op_executed_count <= 32'd0;
    end else if (increment_shift_op_executed) begin
      perf_shift_op_executed_count <= perf_shift_op_executed_count + 1;
    end
  end
  assign cpu_perf_cnt_12 = perf_shift_op_executed_count;

  // cnt_13: NOP Instructions Encountered in ID
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_nop_in_id_count <= 32'd0;
    end else if (increment_nop_in_id) begin
      perf_nop_in_id_count <= perf_nop_in_id_count + 1;
    end
  end
  assign cpu_perf_cnt_13 = perf_nop_in_id_count;

  // cnt_14: Total Memory Operations (Load + Store issued to EX)
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_total_mem_ops_count <= 32'd0;
    end else if (increment_total_mem_ops) begin
      perf_total_mem_ops_count <= perf_total_mem_ops_count + 1;
    end
  end
  assign cpu_perf_cnt_14 = perf_total_mem_ops_count;

  // cnt_15: Register File Writes
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      perf_reg_writes_count <= 32'd0;
    end else if (increment_reg_writes) begin
      perf_reg_writes_count <= perf_reg_writes_count + 1;
    end
  end
  assign cpu_perf_cnt_15 = perf_reg_writes_count;

endmodule


//==============================================================================
// Module: pc (Remains unchanged)
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
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      pc <= 32'h00000000;
    end else if (pc_write_enable) begin
      pc <= next_pc;
    end
  end
endmodule



