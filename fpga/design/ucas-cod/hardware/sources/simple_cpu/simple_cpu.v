// timescale directive: simulation time unit is 10ns, precision is 1ns
`timescale 10ns / 1ns

// Macro definitions for bus widths
`define ADDR_WIDTH 5  // Register file address width
`define DATA_WIDTH 32 // Data bus width

//==============================================================================
// Module: simple_cpu
// Description: A simple MIPS-like CPU core.
//==============================================================================
module simple_cpu (
    //-- Global Signals --
    input         clk,         // Clock signal
    input         rst,         // Reset signal

    //-- Instruction Fetch Interface --
    output [31:0] PC,          // Program Counter output
    input  [31:0] Instruction, // Instruction input from memory

    //-- Data Memory Interface --
    output [31:0] Address,     // Memory address output
    output        MemWrite,    // Memory write enable signal
    output [31:0] Write_data,  // Data to write to memory
    output [ 3:0] Write_strb,  // Memory byte strobes for writes
    input  [31:0] Read_data,   // Data read from memory
    output        MemRead      // Memory read enable signal
);

  //----------------------------------------------------------------------------
  // Instruction Decoding Signals
  //----------------------------------------------------------------------------
  wire [ 5:0] opcode   = Instruction[31:26]; // Opcode field
  wire [ 4:0] rs       = Instruction[25:21]; // Source register 1 specifier
  wire [ 4:0] rt       = Instruction[20:16]; // Source register 2 specifier
  wire [ 4:0] rd       = Instruction[15:11]; // Destination register specifier (R-type)
  wire [ 4:0] shamt    = Instruction[10: 6]; // Shift amount (R-type shift)
  wire [ 5:0] funct    = Instruction[ 5: 0]; // Function field (R-type)
  wire [15:0] imm_16   = Instruction[15: 0]; // 16-bit immediate value (I-type, J-type)

  //----------------------------------------------------------------------------
  // Internal Wires - Connecting Modules
  //----------------------------------------------------------------------------

  //-- Control Signals --
  wire [ 1:0] reg_dst_input;      // Control -> RegWriteCtrl: Selects destination register (rd/rt/ra)
  wire [ 1:0] is_jump_cond;       // Control -> PC Ctrl: Indicates Jump type (None, J, JAL)
  wire        is_branch;          // Control -> PC Ctrl, Branch Ctrl, ALU Src Sel: Indicates Branch instruction
  wire        mem_read;           // Control -> Mem Ctrl, MemToReg: Memory read enable (internal)
  wire        mem_write;          // Control -> Mem Ctrl: Memory write enable (internal)
  wire        alu_src_imm_input;  // Control -> ALU Src Sel: Selects ALU source 2 (Reg/Imm)
  wire        reg_write_cond;     // Control -> RegWriteCtrl: Precondition for register write enable
  wire        alu_op_ok;          // Control -> Arith Ctrl, ALU Op Gen: Indicates ALUOp can be derived from opcode
  wire [ 2:0] alu_op_cond;        // Control -> Arith Ctrl, ALU Op Gen: ALU operation hint from opcode

  //-- Register File Interface (Required for Testbench) --
  wire        RF_wen;             // RegWriteSigGen -> RegFile: Final write enable
  wire [ 4:0] RF_waddr;           // RegWriteCtrl -> RegFile: Write address
  wire [31:0] RF_wdata;           // MemToReg -> RegFile: Write data

  //-- PC Control Path --
  wire [31:0] next_pc;            // PC Ctrl -> PC: Next program counter value
  wire [31:0] current_pc;         // PC -> All: Current program counter value
  wire [31:0] pc_store;           // PC Ctrl -> MemToReg: PC+8 for JAL/JALR link address
  wire        is_jump;            // PC Ctrl -> MemToReg: Indicates any Jump instruction occurred

  //-- Register File Data Path --
  wire [31:0] RF_rdata1;          // RegFile -> ALU Src Sel, Shifter Src Sel, PC Ctrl, MemToReg: Read data 1 (rs)
  wire [31:0] RF_rdata2;          // RegFile -> ALU Src Sel, Shifter Src Sel, Mem Ctrl: Read data 2 (rt)

  //-- ALU/Shifter Path --
  wire        is_shamt;           // Arith Ctrl -> Shifter Src Sel: Indicates shamt is used for shift amount
  wire [ 2:0] alu_op;             // Arith Ctrl -> ALU Op Gen: ALU operation for R-type/I-type Arithmetic
  wire [ 1:0] shifter_op;         // Arith Ctrl -> Shifter: Shift operation type
  wire        is_alu_operation;   // Arith Ctrl -> ALU Op Gen, MemToReg: Indicates an ALU operation is performed
  wire        is_shift_operation; // Arith Ctrl -> MemToReg: Indicates a Shift operation is performed
  wire [31:0] alu_src1;           // ALU Src Sel -> ALU: First ALU operand
  wire [31:0] alu_src2;           // ALU Src Sel -> ALU: Second ALU operand
  wire [31:0] shifter_src1;       // Shifter Src Sel -> Shifter: First Shifter operand
  wire [31:0] shifter_src2;       // Shifter Src Sel -> Shifter: Second Shifter operand (shift amount)
  wire [ 2:0] alu_op_final;       // ALU Op Gen -> ALU: Final ALU operation control
  wire [31:0] alu_result;         // ALU -> PC Ctrl, Mem Ctrl, MemToReg: ALU computation result
  wire        alu_zero;           // ALU -> PC Ctrl, RegWriteSigGen: ALU Zero flag
  wire [31:0] shift_result;       // Shifter -> MemToReg: Shifter result

  //-- Branch Control Path --
  wire        is_zero_cmp;        // Branch Ctrl -> ALU Src Sel: Indicates branch compares rs against zero

  //-- Load/Store Path --
  wire [31:0] load_data;          // Mem Ctrl -> MemToReg: Data processed from memory/registers for load operations

  //-- Move/LUI Path --
  wire        is_move;            // Move/LUI Ctrl -> ALU Op Gen, ALU Src Sel, MemToReg: Indicates MOVZ/MOVN
  wire        is_lui;             // Move/LUI Ctrl -> MemToReg: Indicates LUI instruction
  wire [ 2:0] move_alu_op;        // Move/LUI Ctrl -> ALU Op Gen: ALU operation for MOVZ/MOVN

  //-- Writeback Path --
  wire        reg_write_input;    // RegWriteCtrl -> RegWriteSigGen: Intermediate write enable signal

  //----------------------------------------------------------------------------
  // Module Instantiations (Ordered by logical pipeline stage)
  //----------------------------------------------------------------------------

  //-- STAGE 1: Instruction Fetch (IF) --
  pc instance_pc (
      .clk        (clk),
      .rst        (rst),
      .next_pc    (next_pc),      // Input: Next PC value from PC Controller
      .pc         (current_pc)    // Output: Current PC value
  );

  //-- STAGE 2: Instruction Decode & Register Fetch (ID) --
  control_unit instance_control_unit (
      .opcode       (opcode),           // Input: Instruction opcode
      .reg_dst      (reg_dst_input),    // Output: Destination register select control
      .is_jump      (is_jump_cond),     // Output: Jump type control
      .is_branch    (is_branch),        // Output: Branch instruction indicator
      .mem_read     (mem_read),         // Output: Memory read control
      .alu_op_cond  (alu_op_cond),      // Output: ALU operation hint from opcode
      .alu_op_ok    (alu_op_ok),        // Output: Indicates alu_op_cond is valid
      .mem_write    (mem_write),        // Output: Memory write control
      .alu_src_imm  (alu_src_imm_input),// Output: ALU source 2 is immediate control
      .reg_write_cond(reg_write_cond)   // Output: Register write precondition
  );

  reg_file instance_reg_file (
      .clk        (clk),
      .waddr      (RF_waddr),     // Input: Write address from Reg Write Controller
      .raddr1     (rs),           // Input: Read address 1 (rs field)
      .raddr2     (rt),           // Input: Read address 2 (rt field)
      .wen        (RF_wen),       // Input: Write enable from Reg Write Signal Generator
      .wdata      (RF_wdata),     // Input: Write data from MemToReg Mux
      .rdata1     (RF_rdata1),    // Output: Read data 1 (rs value)
      .rdata2     (RF_rdata2)     // Output: Read data 2 (rt value)
  );

  //-- STAGE 3: Execute (EX) --
  // Determine ALU/Shifter operation details based on instruction type
  arithmetic_controller instance_arithmetic_controller (
      .opcode             (opcode),           // Input: Instruction opcode
      .funct              (funct),            // Input: Instruction function field
      .alu_op_input       (alu_op_cond),      // Input: ALU Op hint from Control Unit
      .alu_op_ok          (alu_op_ok),        // Input: Indicates alu_op_input is valid
      .is_shamt           (is_shamt),         // Output: Select shamt as shift amount source
      .alu_op             (alu_op),           // Output: Decoded ALU operation
      .shifter_op         (shifter_op),       // Output: Decoded Shifter operation
      .is_alu_operation   (is_alu_operation), // Output: Indicates ALU will be used
      .is_shift_operation (is_shift_operation) // Output: Indicates Shifter will be used
  );

  // Determine specific branch conditions (e.g., compare with zero)
  branch_controller instance_branch_controller (
      .opcode        (opcode),        // Input: Instruction opcode
      .funct         (funct),         // Input: Instruction function field (for BLTZ/BGEZ)
      .is_branch     (is_branch),     // Input: Branch indicator from Control Unit
      .is_zero_cmp   (is_zero_cmp)    // Output: Indicates branch compares rs with zero
  );

  // Determine specific move/LUI conditions
  move_and_load_imm_alu_controller instance_move_and_load_imm_alu_controller (
      .opcode       (opcode),       // Input: Instruction opcode
      .funct        (funct),        // Input: Instruction function field
      .is_move      (is_move),      // Output: Indicates MOVZ/MOVN instruction
      .is_lui       (is_lui),       // Output: Indicates LUI instruction
      .move_alu_op  (move_alu_op)   // Output: ALU operation for MOVZ/MOVN
  );

  // Select sources for the ALU
  alu_src_selector instance_alu_src_selector (
      .opcode               (opcode),             // Input: Instruction opcode
      .funct                (funct),              // Input: Instruction function field (for MOVZ/MOVN)
      .alu_src_imm_input    (alu_src_imm_input),  // Input: Control signal for immediate source
      .is_branch            (is_branch),          // Input: Branch indicator
      .is_branch_zero_cmp   (is_zero_cmp),        // Input: Zero comparison branch indicator
      .imm_16               (imm_16),             // Input: 16-bit immediate value
      .rs                   (RF_rdata1),          // Input: Data from register rs
      .rt                   (RF_rdata2),          // Input: Data from register rt
      .alu_src1             (alu_src1),           // Output: ALU operand 1
      .alu_src2             (alu_src2)            // Output: ALU operand 2 (register or immediate)
  );

  // Select sources for the Shifter
  shifter_src_selector instance_shifter_src_selector (
      .rs             (RF_rdata1),    // Input: Data from register rs (for variable shifts)
      .rt             (RF_rdata2),    // Input: Data from register rt (data to be shifted)
      .shamt          (shamt),        // Input: 5-bit shift amount from instruction
      .is_shamt       (is_shamt),     // Input: Control signal to select shamt or rs for shift amount
      .shifter_src1   (shifter_src1), // Output: Shifter operand 1 (data)
      .shifter_src2   (shifter_src2)  // Output: Shifter operand 2 (shift amount)
  );

  // Generate the final ALU operation code based on various instruction types
  alu_op_generator instance_alu_op_generator (
      .alu_op_cond      (alu_op_cond),      // Input: ALU Op hint from Control Unit
      .alu_op_ok        (alu_op_ok),        // Input: Indicates alu_op_cond is valid
      .alu_op           (alu_op),           // Input: ALU Op from Arithmetic Controller
      .is_alu_operation (is_alu_operation), // Input: Indicates an ALU operation is needed
      .is_move          (is_move),          // Input: Indicates a MOVZ/MOVN operation
      .move_alu_op      (move_alu_op),      // Input: ALU Op for MOVZ/MOVN
      .alu_op_final     (alu_op_final)      // Output: Final ALU operation code to ALU
  );

  // Arithmetic Logic Unit
  alu instance_alu (
      .A          (alu_src1),     // Input: Operand 1 from ALU Source Selector
      .B          (alu_src2),     // Input: Operand 2 from ALU Source Selector
      .ALUop      (alu_op_final), // Input: Final ALU operation code
      .Overflow   (),             // Output: Overflow flag (unused)
      .CarryOut   (),             // Output: Carry Out flag (unused)
      .Zero       (alu_zero),     // Output: Zero flag (result is zero)
      .Result     (alu_result)    // Output: ALU computation result
  );

  // Shifter Unit
  shifter instance_shifter (
      .A          (shifter_src1),     // Input: Data operand from Shifter Source Selector
      .B          (shifter_src2[4:0]),// Input: Shift amount [4:0] from Shifter Source Selector
      .Shiftop    (shifter_op),       // Input: Shift operation type from Arithmetic Controller
      .Result     (shift_result)      // Output: Shifter result
  );

  // Calculate the next PC value (handles increments, branches, jumps)
  pc_controller instance_pc_controller (
      .is_branch    (is_branch),        // Input: Branch indicator from Control Unit
      .current_pc   (current_pc),       // Input: Current PC value
      .rs           (RF_rdata1),        // Input: Data from register rs (for JR/JALR)
      .alu_result   (alu_result),       // Input: ALU result (for branch comparison)
      .alu_zero     (alu_zero),         // Input: ALU zero flag (for BEQ/BNE, MOVZ/MOVN conditions)
      .instruction  (Instruction),      // Input: Full instruction for J-type target calculation
      .is_jump      (is_jump),          // Output: Indicates any jump occurred (for MemToReg Mux)
      .next_pc      (next_pc),          // Output: Calculated next PC value
      .pc_store     (pc_store)          // Output: PC+8 for link address storage (JAL/JALR)
  );

  //-- STAGE 4: Memory Access (MEM) --
  // Controls memory accesses (Load/Store) and formats data
  load_and_store_controller instance_load_and_store_controller (
      .opcode      (opcode),        // Input: Instruction opcode
      .mem_addr    (alu_result),    // Input: Memory address (usually from ALU result)
      .mem_data    (Read_data),     // Input: Data read from external memory
      .rf_rdata2   (RF_rdata2),     // Input: Data from register rt (for Store, LWL/LWR)
      .load_data   (load_data),     // Output: Processed data for loads (to MemToReg Mux)
      .mem_addr_o  (Address),       // Output: Memory address to external memory
      .mem_wdata   (Write_data),    // Output: Data to write to external memory
      .mem_strb    (Write_strb)     // Output: Byte strobes for external memory writes
  );

  //-- STAGE 5: Write Back (WB) --
  // Determines the final destination register address
  reg_write_controller instance_reg_write_controller (
      .opcode             (opcode),           // Input: Instruction opcode
      .funct              (funct),            // Input: Instruction function field
      .rd                 (rd),               // Input: rd field from instruction
      .rt                 (rt),               // Input: rt field from instruction
      .input_reg_write_cond(reg_write_cond),  // Input: Write precondition from Control Unit
      .reg_dst_input      (reg_dst_input),    // Input: Destination select control from Control Unit
      .reg_dst            (RF_waddr),         // Output: Final write address to Register File
      .reg_write          (reg_write_input)   // Output: Intermediate write enable signal
  );

  // Generates the final register file write enable signal (handles MOVZ/MOVN)
  reg_write_signal_generator instance_reg_write_signal_generator (
      .reg_write_input (reg_write_input), // Input: Intermediate write enable from Reg Write Controller
      .opcode          (opcode),          // Input: Instruction opcode
      .funct           (funct),           // Input: Instruction function field
      .is_zero         (alu_zero),        // Input: ALU zero flag (for MOVZ/MOVN condition)
      .wen             (RF_wen)           // Output: Final write enable to Register File
  );

  // Selects the data to be written back to the register file
  mem_to_reg instance_mem_to_reg (
      .is_alu_operation   (is_alu_operation), // Input: ALU operation indicator
      .is_shift_operation (is_shift_operation),// Input: Shift operation indicator
      .memread            (mem_read),         // Input: Memory read indicator
      .is_jump            (is_jump),          // Input: Jump instruction indicator (for link address)
      .is_lui             (is_lui),           // Input: LUI instruction indicator
      .is_move            (is_move),          // Input: MOVZ/MOVN instruction indicator
      .alu_result         (alu_result),       // Input: Result from ALU
      .shift_result       (shift_result),     // Input: Result from Shifter
      .mem_data           (load_data),        // Input: Processed data from Load/Store Controller
      .pc_store           (pc_store),         // Input: PC+8 for link address
      .imm_16             (imm_16),           // Input: 16-bit immediate (for LUI)
      .rs                 (RF_rdata1),        // Input: Data from register rs (for MOVZ/MOVN)
      .write_data         (RF_wdata)          // Output: Data to write back to Register File
  );

  //----------------------------------------------------------------------------
  // Top-Level Output Assignments
  //----------------------------------------------------------------------------
  assign PC       = current_pc; // Output the current Program Counter
  assign MemWrite = mem_write;  // Pass through memory write control signal
  assign MemRead  = mem_read;   // Pass through memory read control signal

endmodule


//==============================================================================
// Module: control_unit
// Description: Decodes the opcode to generate control signals for the datapath.
//==============================================================================
module control_unit (
    input  [ 5:0] opcode,       // Input: Instruction opcode field
    output [ 1:0] reg_dst,      // Output: Selects destination register (11=rd, 10=ra(JAL), 01=rt)
    output [ 1:0] is_jump,      // Output: Jump type (00=No, 01=J, 10=JAL)
    output        is_branch,    // Output: Indicates a branch instruction
    output        mem_read,     // Output: Memory read enable for Load instructions
    output [ 2:0] alu_op_cond,  // Output: ALU operation hint derived from opcode (for I-type, Branch, Load/Store)
    output        alu_op_ok,    // Output: Indicates alu_op_cond is valid
    output        mem_write,    // Output: Memory write enable for Store instructions
    output        alu_src_imm,  // Output: Selects immediate as ALU source 2
    output        reg_write_cond// Output: Precondition for register write enable (excludes Stores, Branches, J, JR)
);
  // reg_dst: Select destination register based on instruction type
  // R-type (opcode=0) uses rd, JAL uses $ra (31), others use rt
  assign reg_dst = (opcode == 6'b000000) ? 2'b11 : // R-type (use rd)
                 (opcode == 6'b000011) ? 2'b10 : // JAL (use $ra)
                 (opcode == 6'b000010) ? 2'b00 : // J (no write) - Covered by reg_write_cond anyway
                 2'b01;                          // I-type/Loads (use rt)

  // is_branch: Detect branch instructions (BEQ, BNE, BLEZ, BGTZ, BLTZ, BGEZ)
  wire is_branch_sub = (opcode[5:2] == 4'b0001) ? 1'b1 : 1'b0; // BEQ, BNE, BLEZ, BGTZ
  wire is_branch_slt = (opcode == 6'b000001) ? 1'b1 : 1'b0; // BLTZ, BGEZ (uses REGIMM field)
  assign is_branch = (is_branch_sub || is_branch_slt);

  // mem_read: Asserted for Load instructions (opcode 100xxx)
  assign mem_read = (opcode[5:3] == 3'b100);

  // mem_write: Asserted for Store instructions (opcode 101xxx)
  assign mem_write = (opcode[5:3] == 3'b101);

  // reg_write_cond: Precondition for writing to register file. Disabled for Stores and Branches.
  // Final wen depends on this AND specific instruction details (e.g., J, JR, MOVZ/N conditions).
  assign reg_write_cond = (opcode[5:3] != 3'b101 && !is_branch); // Not Store and not Branch

  // alu_src_imm: Select immediate value as ALU source 2 for I-type arithmetic, Loads, Stores
  assign alu_src_imm = (opcode[5:3] == 3'b001 || opcode[5:3] == 3'b100 || opcode[5:3] == 3'b101);

  // is_jump: Detect J and JAL instructions
  assign is_jump = (opcode == 6'b000010) ? 2'b01 : // J
                   (opcode == 6'b000011) ? 2'b10 : // JAL
                   2'b00;                         // Not J or JAL

  // alu_op_ok & alu_op_cond: Provide ALU operation hint for non-R-type instructions
  wire imm_arithmetic = (opcode[5:3] == 3'b001 && opcode != 6'b001111); // I-type Arith/Logic (ADDIU, SLTI, SLTIU, ANDI, ORI, XORI), excludes LUI
  wire is_load_store  = (opcode[5:3] == 3'b100 || opcode[5:3] == 3'b101); // Load or Store

  // Decode I-type arithmetic operations for alu_op_cond
  wire addiu = (opcode == 6'b001001);
  wire slti  = (opcode == 6'b001010);
  wire sltiu = (opcode == 6'b001011);
  wire andi  = (opcode == 6'b001100);
  wire ori   = (opcode == 6'b001101);
  wire xori  = (opcode == 6'b001110);

  wire [2:0] arith_type = addiu ? 3'b010 : // ADD
                          slti  ? 3'b111 : // SLT
                          sltiu ? 3'b011 : // SLTU
                          andi  ? 3'b000 : // AND
                          ori   ? 3'b001 : // OR
                          xori  ? 3'b100 : // XOR
                          3'bxxx;          // Should not happen for imm_arithmetic

  // Determine alu_op_cond based on instruction type
  // Used by ALUOp Generator if alu_op_ok is true.
  assign alu_op_cond = is_branch_slt ? 3'b111 : // SLT for BLTZ/BGEZ (internally checks sign bit)
                       is_branch_sub ? 3'b110 : // SUB for BEQ/BNE/BLEZ/BGTZ (checks zero/sign)
                       is_load_store ? 3'b010 : // ADD for address calculation
                       imm_arithmetic ? arith_type :
                       3'bxxx;                  // R-type (handled by Arithmetic Controller) or other non-ALU ops

  // alu_op_ok: Flag indicating that alu_op_cond is valid (derived from opcode)
  assign alu_op_ok = (imm_arithmetic || is_branch || is_load_store);

endmodule


//==============================================================================
// Module: reg_write_controller
// Description: Determines the final register destination address and generates
//              an intermediate register write enable signal (before MOVZ/N check).
//==============================================================================
module reg_write_controller (
    input  [ 5:0] opcode,             // Input: Instruction opcode
    input  [ 5:0] funct,              // Input: Instruction function field
    input  [ 4:0] rd,                 // Input: rd field from instruction
    input  [ 4:0] rt,                 // Input: rt field from instruction
    input         input_reg_write_cond,// Input: Precondition for write enable from Control Unit
    input  [ 1:0] reg_dst_input,      // Input: Destination select control from Control Unit (11=rd, 10=ra, 01=rt)
    output [ 4:0] reg_dst,            // Output: Final destination register address (to Reg File)
    output        reg_write           // Output: Intermediate write enable signal (to Reg Write Signal Gen)
);
  // Detect instructions that never write or have special write conditions
  wire j   = (opcode == 6'b000010);                  // J (never writes)
  wire jal = (opcode == 6'b000011);                  // JAL (writes to $ra)
  wire jr  = (opcode == 6'b000000 && funct == 6'b001000); // JR (never writes)

  // reg_write: Intermediate write enable. True if precondition met AND not J or JR.
  // JAL is handled by precondition=1, reg_dst_input=10.
  // Final wen further gated by MOVZ/N condition.
  assign reg_write = (input_reg_write_cond && !j && !jr);

  // _reg_dst: Masked destination select control based on intermediate write enable
  wire [1:0] _reg_dst = {2{reg_write}} & reg_dst_input;

  // reg_dst: Final destination register address
  assign reg_dst = (_reg_dst == 2'b11) ? rd :        // 11: Use rd (R-type)
                   (_reg_dst == 2'b10) ? 5'b11111 : // 10: Use $ra (31) (JAL)
                   (_reg_dst == 2'b01) ? rt :        // 01: Use rt (I-type, Loads)
                   5'b00000;                         // 00: No write / Don't care

endmodule


//==============================================================================
// Module: arithmetic_controller
// Description: Decodes R-type instructions (funct field) to determine ALU/Shifter
//              operation details. Also flags if ALU or Shifter is used.
//==============================================================================
module arithmetic_controller (
    input  [ 5:0] opcode,       // Input: Instruction opcode
    input  [ 5:0] funct,        // Input: Instruction function field
    input  [ 2:0] alu_op_input, // Input: ALU Op hint from Control Unit (for I-type)
    input         alu_op_ok,    // Input: Indicates alu_op_input is valid
    output        is_shamt,     // Output: Indicates shamt field is used for shift amount
    output [ 2:0] alu_op,       // Output: Decoded ALU operation code
    output [ 1:0] shifter_op,   // Output: Decoded Shifter operation code
    output        is_alu_operation, // Output: Flag indicating ALU is used
    output        is_shift_operation// Output: Flag indicating Shifter is used
);

  // R-type ALU operations (funct[5] == 1) or I-type immediate arithmetic
  assign is_alu_operation = ((opcode == 6'b000000 && funct[5] == 1'b1) || // R-type Arith/Logic
                             (opcode[5:3] == 3'b001 && opcode != 6'b001111)); // I-type Arith/Logic (excl LUI)

  // R-type Shift operations (funct[5:3] == 000)
  assign is_shift_operation = (opcode == 6'b000000 && funct[5:3] == 3'b000);

  // -- Decode R-type ALU operations --
  wire addu = (funct == 6'b100001); // ADDU
  wire subu = (funct == 6'b100011); // SUBU
  wire _and = (funct == 6'b100100); // AND
  wire _or  = (funct == 6'b100101); // OR
  wire _xor = (funct == 6'b100110); // XOR
  wire _nor = (funct == 6'b100111); // NOR
  wire slt  = (funct == 6'b101010); // SLT
  wire sltu = (funct == 6'b101011); // SLTU

  wire [2:0] r_type_arith_op = addu ? 3'b010 : // ADD
                               subu ? 3'b110 : // SUB
                               _and ? 3'b000 : // AND
                               _or  ? 3'b001 : // OR
                               _xor ? 3'b100 : // XOR
                               _nor ? 3'b101 : // NOR (Note: MIPS ALU often implements NOR differently, sometimes as ~(A|B))
                               slt  ? 3'b111 : // SLT
                               sltu ? 3'b011 : // SLTU
                               3'bxxx;         // Default / Other R-type

  // alu_op: Final ALU operation code
  // Priority: R-type decoded funct, then I-type decoded opcode, else default.
  assign alu_op = is_alu_operation ? ( (opcode == 6'b000000) ? r_type_arith_op : // R-type
                                       alu_op_input                               // I-type (use hint from Control)
                                     )
                                   : 3'b000; // Default to ADD if not an ALU op (e.g., for address calc pass-through)

  // -- Decode R-type Shift operations --
  wire sll  = (funct == 6'b000000); // SLL
  wire srl  = (funct == 6'b000010); // SRL
  wire sra  = (funct == 6'b000011); // SRA
  wire sllv = (funct == 6'b000100); // SLLV
  wire srlv = (funct == 6'b000110); // SRLV
  wire srav = (funct == 6'b000111); // SRAV

  wire [1:0] shift_type = sll  ? 2'b00 : // Logical Left
                          srl  ? 2'b10 : // Logical Right
                          sra  ? 2'b11 : // Arithmetic Right
                          sllv ? 2'b00 : // Logical Left
                          srlv ? 2'b10 : // Logical Right
                          srav ? 2'b11 : // Arithmetic Right
                          2'bxx;         // Default / Not a shift

  // shifter_op: Final Shifter operation code
  assign shifter_op = is_shift_operation ? shift_type : 2'b00; // Default if not a shift op

  // is_shamt: Indicates if the shift amount comes from the shamt field (SLL, SRL, SRA)
  assign is_shamt = is_shift_operation && (sll || srl || sra);

endmodule


//==============================================================================
// Module: branch_controller
// Description: Determines if a branch instruction requires comparing rs against zero.
//==============================================================================
module branch_controller (
    input  [ 5:0] opcode,      // Input: Instruction opcode
    input  [ 5:0] funct,       // Input: Instruction function field (unused here but potentially useful)
    input         is_branch,   // Input: Branch indicator from Control Unit
    output        is_zero_cmp  // Output: True for branches comparing rs against zero (BLEZ, BGTZ, BLTZ, BGEZ)
);
  // is_zero_cmp: True for BLEZ, BGTZ (opcode check) and BLTZ, BGEZ (REGIMM opcode check)
  assign is_zero_cmp = is_branch &&
                       (opcode == 6'b000110 || // BLEZ
                        opcode == 6'b000111 || // BGTZ
                        opcode == 6'b000001);  // REGIMM (includes BLTZ, BGEZ)
endmodule


//==============================================================================
// Module: pc_controller
// Description: Calculates the next Program Counter value based on instruction
//              type (increment, branch, jump) and conditions.
//==============================================================================
module pc_controller (
    input is_branch,  // 1 means branch
    input [31:0] current_pc,
    input [31:0] rs,  // this is the rs from register file, we will use this to determine
                      // the next pc in jr instruction
    input [31:0] alu_result,  // this is the result from ALU, we will use this to determine
                              // whether to branch or not
    input alu_zero,  // this is the zero flag from ALU, we will use this to determine
                     // whether to branch or not in beq instruction
    input [31:0] instruction,  // the instruction to be executed
    output is_jump,  // if it is a jump instruction
    output [31:0] next_pc,  // the next pc to be sent to the PC module
    output [31:0] pc_store  // pc + 8, to be stored in the PC module
);
  wire [5:0] opcode = instruction[31:26];
  wire [4:0] funct_branch = instruction[20:16];
  wire beq = (opcode == 6'b000100) ? 1'b1 : 1'b0;  // branch if equal
  wire bne = (opcode == 6'b000101) ? 1'b1 : 1'b0;  // branch if not equal
  wire blez = (opcode == 6'b000110) ? 1'b1 : 1'b0;  // branch if less than or equal to zero
  wire bgtz = (opcode == 6'b000111) ? 1'b1 : 1'b0;  // branch if greater than zero
  wire bltz = (opcode == 6'b000001 && funct_branch == 5'b00000) ? 1'b1 : 1'b0;  // branch if less than zero
  wire bgez = (opcode == 6'b000001 && funct_branch == 5'b00001) ? 1'b1 : 1'b0;  // branch if greater than or equal to zero

  wire branch_condition_satisfied = (beq && alu_zero) ||
                             (bne && !alu_zero) ||
                             (blez && (alu_result[31] == 1 || alu_zero == 1)) ||
                             (bgtz && (alu_result[31] == 0 && alu_zero != 1)) ||
                             (bltz && (alu_result == 1)) ||
                             (bgez && (alu_result == 0));  // check if the branch condition is satisfied

  wire [15:0] imm_B = instruction[15:0];
  wire [31:0] imm_B_ext = {{16{imm_B[15]}}, imm_B};  // sign extend the immediate value
  wire [31:0] next_pc_branch = (branch_condition_satisfied) ? (current_pc + 4) + {imm_B_ext[29:0], 2'b00} : current_pc + 4;  // if branch condition is satisfied, we will branch to the target address

  wire [5:0] funct_jump = instruction[5:0];
  wire j = (opcode == 6'b000010) ? 1'b1 : 1'b0;  // jump instruction
  wire jal = (opcode == 6'b000011) ? 1'b1 : 1'b0;  // jump and link instruction
  wire jr = (opcode == 6'b000000 && funct_jump == 6'b001000) ? 1'b1 : 1'b0;  // jump register instruction
  wire jalr = (opcode == 6'b000000 && funct_jump == 6'b001001) ? 1'b1 : 1'b0;  // jump and link register instruction
  assign is_jump = j || jal || jr || jalr;  // if it is a jump instruction

  wire [25:0] imm_J = instruction[25:0];
  wire [31:0] next_pc_jump = (!jr && !jalr) ? {current_pc[31:28], imm_J, 2'b00} : rs;  // if jr or jalr, we will use rs as the next pc
  assign next_pc = (is_jump) ? next_pc_jump :
                 (is_branch) ? next_pc_branch :
                 current_pc + 4;  // if it is a jump, we will use next_pc_jump, if it is a branch, we will use next_pc_branch, otherwise, we will just increment the current pc by 4

  assign pc_store = (is_jump) ? current_pc + 8 :
                  0;  // if it is a jump or branch, we will store pc + 8, otherwise, we will store pc + 4

endmodule



//==============================================================================
// Module: pc
// Description: Program Counter register. Stores the address of the next
//              instruction to be fetched.
//==============================================================================
module pc (
    input         clk,        // Input: Clock signal
    input         rst,        // Input: Reset signal
    input  [31:0] next_pc,    // Input: Address of the next instruction
    output reg [31:0] pc        // Output: Address of the current instruction
);
  // Sequential logic for PC register
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      pc <= 32'h00000000; // Reset PC to 0 (or typical MIPS reset vector 0xBFC00000)
                          // Using 0 for simplicity based on context.
    end else begin
      pc <= next_pc;      // Update PC with the calculated next address
    end
  end
endmodule


//==============================================================================
// Module: load_and_store_controller
// Description: Handles Load and Store operations, calculating memory addresses,
//              formatting data for writes, and processing data from reads.
//              Implements byte/halfword/word accesses, including LWL/LWR/SWL/SWR.
//==============================================================================
module load_and_store_controller (
    input  [ 5:0] opcode,       // Input: Instruction opcode
    input  [31:0] mem_addr,     // Input: Base address calculated by ALU (rs + imm)
    input  [31:0] mem_data,     // Input: Data read from memory for Load operations
    input  [31:0] rf_rdata2,    // Input: Data from register rt (source for Store, target/merge for LWL/LWR)
    output [31:0] load_data,    // Output: Final data to be written back for Load operations
    output [31:0] mem_addr_o,   // Output: Word-aligned memory address to external memory
    output [31:0] mem_wdata,    // Output: Data to write to external memory for Store operations
    output [ 3:0] mem_strb      // Output: Byte strobes for memory write operations
);
  // -- Opcode Decoding --
  // Load instructions
  wire lb  = (opcode == 6'b100000); // Load Byte
  wire lbu = (opcode == 6'b100100); // Load Byte Unsigned
  wire lh  = (opcode == 6'b100001); // Load Halfword
  wire lhu = (opcode == 6'b100101); // Load Halfword Unsigned
  wire lw  = (opcode == 6'b100011); // Load Word
  wire lwl = (opcode == 6'b100010); // Load Word Left
  wire lwr = (opcode == 6'b100110); // Load Word Right

  // Store instructions
  wire sb  = (opcode == 6'b101000); // Store Byte
  wire sh  = (opcode == 6'b101001); // Store Halfword
  wire sw  = (opcode == 6'b101011); // Store Word
  wire swl = (opcode == 6'b101010); // Store Word Left
  wire swr = (opcode == 6'b101110); // Store Word Right

  // -- Type Grouping --
  wire type_load    = lb | lbu | lh | lhu | lw | lwl | lwr; // Any Load instruction
  wire type_store   = sb | sh | sw | swl | swr;           // Any Store instruction
  wire type_mem_b   = lb | lbu | sb;                      // Byte access
  wire type_mem_h   = lh | lhu | sh;                      // Halfword access
  wire type_mem_w   = lw | sw;                            // Aligned Word access
  wire type_mem_wl  = lwl | swl;                          // Word Left access
  wire type_mem_wr  = lwr | swr;                          // Word Right access

  // -- Address Alignment and Offset --
  wire [ 1:0] addr_offset = mem_addr[1:0]; // Byte offset within the word (0, 1, 2, 3)
  wire       addr_0      = (addr_offset == 2'b00);
  wire       addr_1      = (addr_offset == 2'b01);
  wire       addr_2      = (addr_offset == 2'b10);
  wire       addr_3      = (addr_offset == 2'b11);

  // Memory address output is always word-aligned
  assign mem_addr_o = {mem_addr[31:2], 2'b00};

  // -- Byte Strobe Calculation (mem_strb) --
  // Determine which byte lanes are active for a write operation
  assign mem_strb =
        ({4{sb}} & ( // Store Byte
            (addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0010 : 0) |
            (addr_2 ? 4'b0100 : 0) | (addr_3 ? 4'b1000 : 0)
        )) |
        ({4{sh}} & ( // Store Halfword
            (addr_0 ? 4'b0011 : 0) | (addr_2 ? 4'b1100 : 0)
            // Addr 1/3 are alignment exceptions for SH
        )) |
        ({4{sw}} & ( // Store Word (aligned)
            addr_0 ? 4'b1111 : 4'b0000 // Only if aligned
        )) |
        ({4{swl}} & ( // Store Word Left
            (addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0011 : 0) |
            (addr_2 ? 4'b0111 : 0) | (addr_3 ? 4'b1111 : 0)
        )) |
        ({4{swr}} & ( // Store Word Right
            (addr_0 ? 4'b1111 : 0) | (addr_1 ? 4'b1110 : 0) |
            (addr_2 ? 4'b1100 : 0) | (addr_3 ? 4'b1000 : 0)
        ));

  // -- Memory Write Data Formatting (mem_wdata) --
  // Prepare the 32-bit data word to be written based on the store type and alignment
  assign mem_wdata =
        ({32{sb}} & ( // Store Byte: Replicate byte across all lanes (strobe selects)
            {4{rf_rdata2[7:0]}}
        )) |
        ({32{sh}} & ( // Store Halfword: Replicate halfword across lanes
            {2{rf_rdata2[15:0]}}
        )) |
        ({32{sw}} & ( // Store Word: Use full register data
            rf_rdata2
        )) |
        ({32{swl}} & ( // Store Word Left: Shift data based on address offset
            (addr_0 ? {24'b0, rf_rdata2[31:24]} :           // Write MSB
             addr_1 ? {16'b0, rf_rdata2[31:16]} :           // Write upper 2 bytes
             addr_2 ? { 8'b0, rf_rdata2[31: 8]} :           // Write upper 3 bytes
                      rf_rdata2)                            // Write all 4 bytes
        )) |
        ({32{swr}} & ( // Store Word Right: Shift data based on address offset
            (addr_0 ? rf_rdata2 :                           // Write all 4 bytes
             addr_1 ? {rf_rdata2[23:0],  8'b0} :            // Write lower 3 bytes
             addr_2 ? {rf_rdata2[15:0], 16'b0} :            // Write lower 2 bytes
                      {rf_rdata2[ 7:0], 24'b0})             // Write LSB
        ));


  // -- Load Data Processing (load_data) --
  assign load_data = (lb | lbu) ?  // Load Byte (Signed or Unsigned) (Load 部分保持不变)
      (addr_0 ? {{24{(lb & mem_data [ 7])}}, mem_data [ 7: 0]} :
       addr_1 ? {{24{(lb & mem_data [15])}}, mem_data [15: 8]} :
       addr_2 ? {{24{(lb & mem_data [23])}}, mem_data [23:16]} :
                {{24{(lb & mem_data [31])}}, mem_data [31:24]} ) :

      (lh | lhu) ?  // Load Halfword (Signed or Unsigned)
       (addr_0 ? {{16{(lh & mem_data [15])}}, mem_data [15: 0]} :
       addr_2 ? {{16{(lh & mem_data [31])}}, mem_data [31:16]} :
                32'b0 ) : // Should not happen for properly aligned halfword load

      lw ? mem_data :  // Load Word
       lwl ?  // Load Word Left
       (addr_0 ? {mem_data [ 7: 0], rf_rdata2 [23: 0]} :
       addr_1 ? {mem_data [15: 0], rf_rdata2 [15: 0]} :
       addr_2 ? {mem_data [23: 0], rf_rdata2 [ 7: 0]} :
                mem_data ) :
      lwr ?             // Load Word Right
       (addr_0 ? mem_data :
       addr_1 ? {rf_rdata2 [31:24], mem_data [31: 8]} :
       addr_2 ? {rf_rdata2 [31:16], mem_data [31:16]} :
                {rf_rdata2 [31: 8], mem_data [31:24]} ) :
      32'b0; // Default case, should not be reached

endmodule


//==============================================================================
// Module: move_and_load_imm_alu_controller
// Description: Detects conditional move (MOVZ, MOVN) and Load Upper Immediate (LUI)
//              instructions and provides control signals.
//==============================================================================
module move_and_load_imm_alu_controller (
    input  [ 5:0] opcode,      // Input: Instruction opcode
    input  [ 5:0] funct,       // Input: Instruction function field
    output        is_move,     // Output: Indicates MOVZ or MOVN instruction
    output        is_lui,      // Output: Indicates LUI instruction
    output [ 2:0] move_alu_op  // Output: ALU operation for MOVZ/MOVN (typically OR/ADD with zero)
);
  // Detect conditional move instructions (R-type)
  wire movn = (opcode == 6'b000000 && funct == 6'b001011); // Move if Not Zero (rt != 0)
  wire movz = (opcode == 6'b000000 && funct == 6'b001010); // Move if Zero (rt == 0)
  assign is_move = movn || movz;

  // Define the ALU operation used to effectively pass 'rs' through for MOVZ/MOVN.
  // Using OR with 0 (alu_src1) achieves this: Result = 0 | rs = rs. ADD also works: Result = 0 + rs = rs.
  assign move_alu_op = 3'b001; // OR operation (could also be ADD 3'b010)

  // Detect Load Upper Immediate instruction (I-type)
  assign is_lui = (opcode == 6'b001111); // LUI

endmodule


//==============================================================================
// Module: reg_write_signal_generator
// Description: Generates the final write enable signal for the register file,
//              considering MOVZ/MOVN conditions based on the ALU zero flag.
//==============================================================================
module reg_write_signal_generator (
    input       reg_write_input, // Input: Intermediate write enable from Reg Write Controller
    input [5:0] opcode,          // Input: Instruction opcode
    input [5:0] funct,           // Input: Instruction function field
    input       is_zero,         // Input: ALU zero flag (used for MOVZ/MOVN condition)
    output      wen              // Output: Final Write Enable signal to Register File
);
  // Detect conditional move instructions
  wire movn = (opcode == 6'b000000 && funct == 6'b001011); // Move if Not Zero (rt != 0) -> is_zero should be 0
  wire movz = (opcode == 6'b000000 && funct == 6'b001010); // Move if Zero (rt == 0) -> is_zero should be 1

  // Final write enable logic:
  // Normal write: reg_write_input is true AND it's not a conditional move.
  // MOVN write: Instruction is MOVN AND the condition (rt != 0 -> !is_zero) is met.
  // MOVZ write: Instruction is MOVZ AND the condition (rt == 0 -> is_zero) is met.
  assign wen = (reg_write_input && !movn && !movz) || // Normal write condition
               (movn && !is_zero) ||                  // MOVN condition met
               (movz && is_zero);                     // MOVZ condition met
endmodule


//==============================================================================
// Module: alu_src_selector
// Description: Selects the two source operands for the ALU based on the
//              instruction type (register, immediate, special cases like MOVZ/N).
//==============================================================================
module alu_src_selector (
    input  [ 5:0] opcode,             // Input: Instruction opcode
    input  [ 5:0] funct,              // Input: Instruction function field
    input         alu_src_imm_input,  // Input: Control signal selecting immediate for Src2
    input         is_branch,          // Input: Branch instruction indicator
    input         is_branch_zero_cmp, // Input: Branch compares rs against zero indicator
    input  [15:0] imm_16,             // Input: 16-bit immediate value from instruction
    input  [31:0] rs,                 // Input: Data from register rs
    input  [31:0] rt,                 // Input: Data from register rt
    output [31:0] alu_src1,           // Output: ALU operand 1
    output [31:0] alu_src2            // Output: ALU operand 2
);
  // Immediate value extension
  wire [31:0] imm_SE = {{16{imm_16[15]}}, imm_16}; // Sign-extended immediate
  wire [31:0] imm_0E = {16'b0, imm_16};            // Zero-extended immediate

  // Detect immediate logical operations that require zero extension
  wire andi = (opcode == 6'b001100);
  wire ori  = (opcode == 6'b001101);
  wire xori = (opcode == 6'b001110);
  // Note: SLTIU (opcode 001011) also uses zero extension conceptually for comparison,
  // but the ALU performs signed subtraction/comparison. The standard requires sign extension for SLTIU's immediate operand fed to the ALU.
  // Sticking to explicit ANDI/ORI/XORI for zero extension selection.
  wire use_zero_extend = andi || ori || xori;

  // Select ALU Source 2 (Operand B)
  assign alu_src2 = (is_branch && is_branch_zero_cmp) ? 32'b0 : // For BLEZ, BGTZ etc., compare rs with 0
                    (alu_src_imm_input) ? (use_zero_extend ? imm_0E : imm_SE) : // Immediate (Zero or Sign extended)
                    rt; // Default: Use data from register rt

  // Detect conditional moves for Source 1 modification
  wire movn = (opcode == 6'b000000 && funct == 6'b001011); // Move if Not Zero
  wire movz = (opcode == 6'b000000 && funct == 6'b001010); // Move if Zero
  wire is_move = movn || movz;

  // Select ALU Source 1 (Operand A)
  // For MOVZ/MOVN, use 0 as source 1, ALU performs 0 OR rs to pass rs through.
  assign alu_src1 = (is_move) ? 32'b0 : rs; // Default: Use data from register rs

endmodule


//==============================================================================
// Module: shifter_src_selector
// Description: Selects the two source operands for the Shifter based on the
//              instruction type (rt data, shamt or rs amount).
//==============================================================================
module shifter_src_selector (
    input  [31:0] rs,             // Input: Data from register rs (used for variable shift amount)
    input  [31:0] rt,             // Input: Data from register rt (data to be shifted)
    input  [ 4:0] shamt,          // Input: 5-bit immediate shift amount from instruction
    input         is_shamt,       // Input: Control signal selecting shamt vs rs for shift amount
    output [31:0] shifter_src1,   // Output: Shifter operand 1 (data to shift = rt)
    output [31:0] shifter_src2    // Output: Shifter operand 2 (shift amount = shamt or rs[4:0])
);
  // Shifter Source 1 is always the data from register rt
  assign shifter_src1 = rt;

  // Shifter Source 2 is the shift amount:
  // If is_shamt is true (SLL, SRL, SRA), use the 5-bit shamt field.
  // Otherwise (SLLV, SRLV, SRAV), use the lower 5 bits of register rs.
  assign shifter_src2 = (is_shamt) ? {27'b0, shamt} : {27'b0, rs[4:0]};

endmodule


//==============================================================================
// Module: alu_op_generator
// Description: Selects the final ALU operation code based on control signals
//              from different controller modules (Control Unit, Arithmetic, Move).
//==============================================================================
module alu_op_generator (
    input  [ 2:0] alu_op_cond,      // Input: ALU Op hint from Control Unit (I-type, Load/Store, Branch)
    input         alu_op_ok,        // Input: Indicates alu_op_cond is valid
    input  [ 2:0] alu_op,           // Input: ALU Op from Arithmetic Controller (R-type, I-type arith)
    input         is_alu_operation, // Input: Indicates a primary ALU operation is needed
    input         is_move,          // Input: Indicates a MOVZ/MOVN operation
    input  [ 2:0] move_alu_op,      // Input: Specific ALU Op for MOVZ/MOVN
    output [ 2:0] alu_op_final      // Output: Final ALU operation code to ALU
);
  // Determine the final ALU operation with priority:
  // 1. MOVZ/MOVN: Use the specific move_alu_op.
  // 2. R-type/I-type Arithmetic: Use alu_op from Arithmetic Controller.
  // 3. Load/Store/Branch: Use alu_op_cond hint from Control Unit.
  // 4. Default: ADD (e.g., if no other condition applies, though usually one should).
  assign alu_op_final = (is_move)          ? move_alu_op :   // Priority 1: Move instructions
                        (is_alu_operation) ? alu_op :        // Priority 2: R-type or I-type arithmetic/logic
                        (alu_op_ok)        ? alu_op_cond :   // Priority 3: Load/Store/Branch address calc/compare
                        3'b010;                              // Default: ADD (should ideally not be reached if logic is complete)

endmodule


//==============================================================================
// Module: mem_to_reg
// Description: Multiplexer selecting the final data to be written back to the
//              register file, choosing between ALU result, Shifter result,
//              memory data, PC+8 (link address), LUI immediate, or rs (MOVZ/N).
//==============================================================================
module mem_to_reg (
    input         is_alu_operation,   // Input: ALU operation indicator
    input         is_shift_operation, // Input: Shift operation indicator
    input         memread,            // Input: Memory read indicator (Load instructions)
    input         is_jump,            // Input: Any jump indicator (specifically JAL/JALR need pc_store)
    input         is_lui,             // Input: LUI instruction indicator
    input         is_move,            // Input: MOVZ/MOVN instruction indicator
    input  [31:0] alu_result,         // Input: Result from ALU
    input  [31:0] shift_result,       // Input: Result from Shifter
    input  [31:0] mem_data,           // Input: Processed data from Load/Store Controller (from memory)
    input  [31:0] pc_store,           // Input: PC+8 link address (for JAL/JALR)
    input  [15:0] imm_16,             // Input: 16-bit immediate (for LUI)
    input  [31:0] rs,                 // Input: Data from register rs (source for MOVZ/MOVN)
    output [31:0] write_data          // Output: Final data to write back to Register File
);
  // Construct the LUI result: {imm_16, 16'b0}
  wire [31:0] lui_result = {imm_16, 16'b0};

  // Select the data source for register writeback based on instruction type priority
  assign write_data = (is_lui)             ? lui_result :   // Priority 1: LUI result
                      (memread)            ? mem_data :     // Priority 2: Data loaded from memory
                      (is_alu_operation && !is_move) ? alu_result : // Priority 3: ALU result (excluding moves)
                      (is_shift_operation) ? shift_result : // Priority 4: Shifter result
                      (is_move)            ? rs :           // Priority 5: rs data (for MOVZ/MOVN, passed via ALU)
                      (is_jump)            ? pc_store :     // Priority 6: Link address for JAL/JALR (non-zero only if JAL/JALR)
                      32'b0;                                 // Default: 0 (should not be reached for writing instructions)

endmodule