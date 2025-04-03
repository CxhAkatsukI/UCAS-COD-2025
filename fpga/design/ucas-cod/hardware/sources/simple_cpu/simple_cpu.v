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
  wire        reg_dst_input;      // Control -> RegWriteCtrl: Selects destination register (rd/rt/ra)
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
      .is_branch_zero_cmp   (is_zero_cmp),        // Input: Zero comparison branch indicator
      .is_move              (is_move),            // Input: MOVZ/MOVN instruction indicator
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
  // Determines the final destination register address and wen signal
  reg_write_controller instance_reg_write_controller (
      .opcode             (opcode),           // Input: Instruction opcode
      .funct              (funct),            // Input: Instruction function field
      .rd                 (rd),               // Input: rd field from instruction
      .rt                 (rt),               // Input: rt field from instruction
      .input_reg_write_cond(reg_write_cond),  // Input: Write precondition from Control Unit
      .reg_dst_input      (reg_dst_input),    // Input: Destination select control from Control Unit
      .is_move            (is_move),          // Input: MOVZ/MOVN instruction indicator
      .is_zero            (alu_zero),         // Input: ALU zero flag (for MOVZ/MOVN condition)
      .reg_dst            (RF_waddr),         // Output: Final write address to Register File
      .wen                (RF_wen)            // Output: Final write enable signal
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
    output        reg_dst,      // Output: Selects destination register (rd/rt/ra)
    output        is_branch,    // Output: Indicates a branch instruction
    output        mem_read,     // Output: Memory read enable for Load instructions
    output [ 2:0] alu_op_cond,  // Output: ALU operation hint (I-type, Branch, Load/Store)
    output        alu_op_ok,    // Output: Indicates alu_op_cond is valid
    output        mem_write,    // Output: Memory write enable for Store instructions
    output        alu_src_imm,  // Output: Selects immediate as ALU source 2
    output        reg_write_cond// Output: Precondition for register write enable
);

  //----------------------------------------------------------------------------
  // Register Destination Control (reg_dst)
  //----------------------------------------------------------------------------
  // Select destination register based on instruction type:
  // - R-type: rd
  // - JAL:    ra ($31)
  // - Others: rt (I-type, Loads)
  // Formula: reg_dst = opcode[5] ^ opcode[3]
  assign reg_dst = opcode[5] ^ opcode[3];

  //----------------------------------------------------------------------------
  // Branch Instruction Detection (is_branch)
  //----------------------------------------------------------------------------
  // Detect branch instructions: BEQ, BNE, BLEZ, BGTZ, BLTZ, BGEZ
  wire is_branch_sub = (opcode[5:2] == 4'b0001); // BEQ, BNE, BLEZ, BGTZ (opcode group 0001xx)
  wire is_branch_slt = (opcode == 6'b000001);     // BLTZ, BGEZ (opcode 000001, REGIMM group)
  assign is_branch = (is_branch_sub || is_branch_slt);

  //----------------------------------------------------------------------------
  // Memory Read Control (mem_read)
  //----------------------------------------------------------------------------
  // Assert mem_read for Load instructions (opcode 100xxx)
  assign mem_read = (opcode[5:3] == 3'b100);

  //----------------------------------------------------------------------------
  // Memory Write Control (mem_write)
  //----------------------------------------------------------------------------
  // Assert mem_write for Store instructions (opcode 101xxx)
  assign mem_write = (opcode[5:3] == 3'b101);

  //----------------------------------------------------------------------------
  // Register Write Precondition (reg_write_cond)
  //----------------------------------------------------------------------------
  // Precondition for writing to register file. Disabled for:
  // - Store instructions (opcode 101xxx)
  // - Branch instructions (is_branch)
  // Final register write enable (RF_wen) is further controlled in reg_write_controller.
  assign reg_write_cond = (opcode[5:3] != 3'b101 && !is_branch); // Not Store AND not Branch

  //----------------------------------------------------------------------------
  // ALU Source 2 Selection (alu_src_imm)
  //----------------------------------------------------------------------------
  // Select immediate value as ALU source 2 for:
  // - I-type arithmetic instructions (opcode 001xxx, excluding LUI)
  // - Load instructions (opcode 100xxx)
  // - Store instructions (opcode 101xxx)
  // Formula: alu_src_imm = ((opcode[5] || opcode[3]) && !opcode[4])
  assign alu_src_imm = ((opcode[5] || opcode[3]) && !opcode[4]);

  //----------------------------------------------------------------------------
  // ALU Operation Hint Generation (alu_op_cond & alu_op_ok)
  //----------------------------------------------------------------------------
  // Provide ALU operation hint (alu_op_cond) for non-R-type instructions.
  // Flag (alu_op_ok) indicates if alu_op_cond is valid.

  // Detect I-type arithmetic/logic instructions (excluding LUI)
  wire imm_arithmetic = (opcode[5:3] == 3'b001 && ~&opcode[2:0]); // opcode 001xxx and not LUI (001111)
  // Detect Load or Store instructions
  wire is_load_store = (opcode[5]); // opcode 10xxxx or 11xxxx (only consider 10xxxx for load/store in this CU)

  // Decode I-type arithmetic operation type to generate ALU hint (arith_type)
  wire [2:0] arith_type;
  assign arith_type[0] = (~opcode[2] & opcode[1]) | (opcode[2] & opcode[0]); // Logic for bit 0 of ALU op
  assign arith_type[1] = ~opcode[2];                                      // Logic for bit 1 of ALU op
  assign arith_type[2] = opcode[1] & ~opcode[0];                                     // Logic for bit 2 of ALU op

  // Determine alu_op_cond based on instruction type:
  // - BLTZ/BGEZ:   SLT  (for sign bit check)
  // - BEQ/BNE/BLEZ/BGTZ: SUB  (for zero/sign check)
  // - Load/Store:  ADD  (for address calculation)
  // - I-type Arith: Based on arith_type (ADD, SLT, SLTU, AND, OR, XOR)
  assign alu_op_cond = is_branch_slt ? 3'b111 :      // SLT for BLTZ/BGEZ
                       is_branch_sub ? 3'b110 :      // SUB for BEQ/BNE/BLEZ/BGTZ
                       is_load_store ? 3'b010 :      // ADD for address calculation (Load/Store)
                       imm_arithmetic ? arith_type : // Arith type for I-type arithmetic
                       3'bxxx;                      // Default (R-type or others, not used)

  // alu_op_ok: Flag indicating alu_op_cond is valid for ALUOp Generator
  assign alu_op_ok = (imm_arithmetic || is_branch || is_load_store);

endmodule


//==============================================================================
// Module: reg_write_controller
// Description: Determines the final register destination address and generates
//              the register write enable signal, considering special cases like
//              J, JR, and conditional moves (MOVZ/MOVN).
//==============================================================================
module reg_write_controller (
    input  [ 5:0] opcode,             // Input: Instruction opcode
    input  [ 5:0] funct,              // Input: Instruction function field
    input  [ 4:0] rd,                 // Input: rd field from instruction
    input  [ 4:0] rt,                 // Input: rt field from instruction
    input         input_reg_write_cond,// Input: Precondition for write enable from Control Unit
    input         reg_dst_input,      // Input: Dest register select from Control Unit (rd/rt/ra)
    input         is_zero,            // Input: Zero flag from ALU (for MOVZ/N condition)
    input         is_move,            // Input: Indicates MOVZ or MOVN instruction
    output [ 4:0] reg_dst,            // Output: Final destination register address (to Reg File)
    output        wen                 // Output: Final register write enable signal (to Reg File)
);

  //----------------------------------------------------------------------------
  // Detect Non-Writing Instructions (J, JR)
  //----------------------------------------------------------------------------
  // Identify instructions that never write to the register file:
  // - J (Jump)
  // - JR (Jump Register)
  wire is_j  = (opcode == 6'b000010);             // J instruction detection
  wire is_jr = (~|opcode && funct == 6'b001000);  // JR instruction detection

  //----------------------------------------------------------------------------
  // Intermediate Register Write Condition (reg_write_cond)
  //----------------------------------------------------------------------------
  // Generate an intermediate write enable condition:
  // - Starts with the precondition from the Control Unit (input_reg_write_cond).
  // - Disabled if the instruction is J or JR (instructions that never write).
  // Note: JAL is handled by input_reg_write_cond being asserted and reg_dst_input selecting $ra.
  wire intermediate_reg_write_cond = (input_reg_write_cond && !is_j && !is_jr);

  //----------------------------------------------------------------------------
  // Final Destination Register Address Selection (reg_dst)
  //----------------------------------------------------------------------------
  // Determine the final register destination address based on instruction type
  // and control signals:
  // - If reg_dst_input is asserted:
  //   - For R-type instructions (where reg_dst_input selects 'rd'): use 'rd'.
  //   - For I-type and Load instructions (where reg_dst_input selects 'rt'): use 'rt'.
  // - For JAL instruction (opcode[0] is asserted, and reg_dst_input selects 'ra'): use $ra (register 31).
  // - Default (for instructions that do not write or don't care): use 'rd' (though it won't be written).
  assign reg_dst = (reg_dst_input) ? rt :         // Use 'rt' if reg_dst_input is asserted (I-type, Loads)
                   (opcode[0])     ? 5'b11111 :   // Use $ra (31) for JAL
                                     rd;          // Default or R-type (using 'rd' when reg_dst_input is asserted for R-type)

  //----------------------------------------------------------------------------
  // Final Register Write Enable Signal Generation (wen)
  //----------------------------------------------------------------------------
  // Generate the final register write enable signal (wen):
  // - Enabled if the intermediate write condition is met AND it's NOT a MOVZ/MOVN instruction.
  // - OR, enabled if it IS a MOVZ/MOVN instruction AND the MOVZ/MOVN condition (based on ALU zero flag and funct[0]) is met.
  assign wen = (intermediate_reg_write_cond && !is_move) ||    // Normal write condition (not MOVZ/N)
               (is_move && (funct[0] ^ is_zero));              // MOVZ/MOVN condition is satisfied

endmodule


//==============================================================================
// Module: arithmetic_controller
// Description: Decodes R-type instructions (funct field) to determine ALU and
//              Shifter operation details. Flags whether ALU or Shifter is used.
//==============================================================================
module arithmetic_controller (
    input  [ 5:0] opcode,       // Input: Instruction opcode
    input  [ 5:0] funct,        // Input: Instruction function field (for R-type)
    input  [ 2:0] alu_op_input, // Input: ALU Op hint from Control Unit (for I-type)
    input         alu_op_ok,    // Input: Indicates alu_op_input is valid
    output        is_shamt,     // Output: Indicates shamt field is used for shift amount
    output [ 2:0] alu_op,       // Output: Decoded ALU operation code
    output [ 1:0] shifter_op,   // Output: Decoded Shifter operation code
    output        is_alu_operation, // Output: Flag indicating ALU is used
    output        is_shift_operation// Output: Flag indicating Shifter is used
);

  //----------------------------------------------------------------------------
  // Operation Type Flags: ALU and Shifter Usage
  //----------------------------------------------------------------------------
  // is_alu_operation: Flag for ALU operations.
  // ALU is used for:
  //   - R-type arithmetic and logic instructions (funct[5] == 1).
  //   - I-type arithmetic and logic instructions (opcode 001xxx, excluding LUI).
  assign is_alu_operation = ((~|opcode && funct[5] == 1'b1) || // R-type Arithmetic/Logic
                             (opcode[5:3] == 3'b001 && ~&opcode[2:0])); // I-type Arithmetic/Logic (excluding LUI)

  // is_shift_operation: Flag for Shifter operations.
  // Shifter is used for:
  //   - R-type shift instructions (funct[5:3] == 000).
  assign is_shift_operation = (~|opcode && ~|funct[5:3]); // R-type Shift operations

  //----------------------------------------------------------------------------
  // ALU Operation Decoding (alu_op)
  //----------------------------------------------------------------------------
  // r_type_arith_op: Decodes the funct field for R-type arithmetic/logic operations
  wire [2:0] r_type_arith_op;
  assign r_type_arith_op[0] = (funct[3] & funct[1]) | (~funct[3] & funct[2] & funct[0]);
  assign r_type_arith_op[1] = funct[3] | ~funct[2];
  assign r_type_arith_op[2] = (funct[3] & ~funct[0]) | (~funct[3] & funct[1]);
  // ALU Operation Code Selection (alu_op):
  // Determines the final ALU operation code based on instruction type priority:
  // 1. R-type instructions: Use decoded `r_type_arith_op` based on funct field.
  // 2. I-type instructions (arithmetic/logic): Use `alu_op_input` hint from Control Unit.
  // 3. Default: ADD operation (3'b010) if no ALU operation is explicitly detected.
  assign alu_op = is_alu_operation ? ( (~|opcode) ? r_type_arith_op : // R-type ALU operation
                                       alu_op_input                  // I-type ALU operation (from Control Unit hint)
                                     )
                                   : 3'b010; // Default to ADD if not an ALU operation (e.g., for pass-through)

  //----------------------------------------------------------------------------
  // Shifter Operation Decoding (shifter_op) and shamt Selection (is_shamt)
  //----------------------------------------------------------------------------
  // shift_type: Decodes the funct field for R-type shift operations.
  wire [1:0] shift_type;
  assign shift_type[0] = funct[1] & funct[0];
  assign shift_type[1] = funct[1];
  // Shifter Operation Code Selection (shifter_op):
  // Selects the final Shifter operation code.
  // If it's a shift operation, use decoded `shift_type`, otherwise default to 2'b00 (SLL - Logical Left, though default doesn't matter if shifter is not used).
  assign shifter_op = is_shift_operation ? shift_type : 2'b00; // Default if not a shift operation

  // is_shamt: Shamt field usage indicator.
  // Indicates if the shift amount for the Shifter should come from the `shamt` field of the instruction.
  // This is true for SLL, SRL, SRA (R-type shifts with immediate shift amount).
  assign is_shamt = is_shift_operation && ~funct[2]; // shamt used when funct[2] is 0 in shift instructions

endmodule


//==============================================================================
// Module: branch_controller
// Description: Determines if a branch instruction requires comparing rs against zero.
//==============================================================================
module branch_controller (
    input  [ 5:0] opcode,      // Input: Instruction opcode
    input         is_branch,   // Input: Branch indicator from Control Unit
    output        is_zero_cmp  // Output: True for branches comparing rs against zero (BLEZ, BGTZ, BLTZ, BGEZ)
);
  // is_zero_cmp: True for BLEZ, BGTZ (opcode check) and BLTZ, BGEZ (REGIMM opcode check)
  assign is_zero_cmp = is_branch &&
                       (opcode[2:0] == 3'b110 || // BLEZ
                        opcode[2:0] == 3'b111 || // BGTZ
                        opcode[2:0] == 3'b001);  // REGIMM (includes BLTZ, BGEZ)
endmodule


//==============================================================================
// Module: pc_controller
// Description: Calculates the next Program Counter (PC) value based on the
//              current instruction type and execution conditions. Handles:
//              - Sequential instruction fetching (PC + 4)
//              - Branch instructions (conditional PC update)
//              - Jump instructions (unconditional PC update)
//              - Jump Register (JR/JALR) instructions
//==============================================================================
module pc_controller (
    input         is_branch,   // Input: Branch instruction signal from Control Unit
    input  [31:0] current_pc,  // Input: Current Program Counter value
    input  [31:0] rs,          // Input: Value of register rs (for JR and JALR instructions)
    input  [31:0] alu_result,  // Input: Result from ALU (used for branch condition evaluation)
    input         alu_zero,    // Input: Zero flag from ALU (used for BEQ, BNE branch conditions)
    input  [31:0] instruction, // Input: Full instruction word
    output        is_jump,     // Output: Indicates if the current instruction is a jump instruction
    output [31:0] next_pc,     // Output: Calculated next Program Counter value
    output [31:0] pc_store     // Output: Value to store for PC update (e.g., PC+8 for JAL/JALR link address)
);

  //----------------------------------------------------------------------------
  // Instruction Decoding Wires
  //----------------------------------------------------------------------------
  wire [5:0] opcode       = instruction[31:26]; // Opcode field of the instruction
  wire [4:0] funct_branch = instruction[20:16]; // Function field (bits 16-20) for branch instructions
  wire [5:0] funct_jump   = instruction[5:0];  // Function field (bits 0-5) for jump instructions
  wire [15:0] imm_B        = instruction[15:0]; // 16-bit immediate for branch instructions
  wire [25:0] imm_J        = instruction[25:0]; // 26-bit immediate for jump instructions

  //----------------------------------------------------------------------------
  // Branch Instruction Handling
  //----------------------------------------------------------------------------
  // branch_condition_satisfied: Determines if the branch condition is met based on:
  // - Opcode bits for branch type (BEQ, BNE, BLEZ, BGTZ, BLTZ, BGEZ)
  // - funct_branch field for REGIMM branches (BLTZ, BGEZ)
  // - ALU zero flag (alu_zero) for BEQ, BNE
  // - ALU result sign bit (alu_result[31]) and zero flag for BLEZ, BGTZ, BLTZ, BGEZ
  //
  // New Logic Formula for branch_condition_satisfied (more compact and efficient):
  // -  !opcode[2] && (funct_branch[0] ^ alu_result)        :  BLTZ/BGEZ  (REGIMM, funct_branch[0] distinguishes BLTZ/BGEZ, alu_result is sign bit)
  // -  opcode[1]  && (opcode[0] ^ (alu_result[31] || alu_zero)): BLEZ/BGTZ (opcode[0] distinguishes BLEZ/BGTZ, checks sign or zero)
  // - (opcode[2]^opcode[1]) && (opcode[0] ^ alu_zero)      : BEQ/BNE    (opcode[0] distinguishes BEQ/BNE, checks zero flag)
  wire branch_condition_satisfied = (!opcode[2] && (funct_branch[0] ^ alu_result)) ||
                                    (opcode[1] && (opcode[0] ^ (alu_result[31] || alu_zero))) ||
                                    ((opcode[2] ^ opcode[1]) && (opcode[0] ^ alu_zero));

  // imm_B_ext: Sign-extend the 16-bit branch immediate to 32 bits
  wire [31:0] imm_B_ext = {{16{imm_B[15]}}, imm_B};
  // next_pc_branch: Calculate the branch target address if the condition is satisfied,
  //                  otherwise, just increment PC by 4 for sequential execution.
  wire [31:0] next_pc_branch = (branch_condition_satisfied) ? (current_pc + 4) + {imm_B_ext[29:0], 2'b00} : current_pc + 4;

  //----------------------------------------------------------------------------
  // Jump Instruction Handling
  //----------------------------------------------------------------------------
  // is_jump: Detects Jump (J, JAL, JR, JALR) instructions.
  // New Logic Formula for is_jump (more compact):
  // - (~|opcode && funct_jump[3] == 1'b1 && funct_jump[1] == 1'b0): JR/JALR (R-type, funct[3:2] == 01)
  // - (~|opcode[5:2] && opcode[1] == 1'b1)             : J/JAL   (opcode[5:2] == 0000, opcode[1] == 1)
  assign is_jump = (~|opcode && funct_jump[3] == 1'b1 && funct_jump[1] == 1'b0) ||
                   (~|opcode[5:2] && opcode[1] == 1'b1);

  // next_pc_jump: Calculate the jump target address based on jump type:
  // - J and JAL:  {current_pc[31:28], imm_J, 2'b00} (PC-relative jump)
  // - JR and JALR: rs (jump to address in register rs)
  wire [31:0] next_pc_jump = (|opcode) ? {current_pc[31:28], imm_J, 2'b00} : rs;

  //----------------------------------------------------------------------------
  // Next PC Selection and PC Store Value
  //----------------------------------------------------------------------------
  // next_pc: Select the next PC value based on instruction type priority:
  // 1. Jump instruction (is_jump): Use calculated jump target address (next_pc_jump).
  // 2. Branch instruction (is_branch): Use calculated branch target address (next_pc_branch).
  // 3. Sequential execution (default): Increment current PC by 4 (current_pc + 4).
  assign next_pc = (is_jump)    ? next_pc_jump    :
                   (is_branch)  ? next_pc_branch  :
                                  current_pc + 4;

  // pc_store: Determine the value to store for PC update (used for JAL/JALR link address):
  // - For Jump instructions (is_jump): store current_pc + 8 (return address for link).
  // - Otherwise: store 0 (or don't care as it's not used for other instruction types).
  assign pc_store = (is_jump) ? current_pc + 8 :
                               0;

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
// Description: Handles Load and Store operations for a MIPS-like architecture.
//              Performs memory address calculation (offset from ALU), data
//              formatting for writes, and data processing for reads, supporting:
//              - Byte, Halfword, and Word accesses (LB, LBU, LH, LHU, LW, SB, SH, SW)
//              - Unaligned Word accesses (LWL, LWR, SWL, SWR)
//==============================================================================
module load_and_store_controller (
    input  [ 5:0] opcode,       // Input: Instruction opcode
    input  [31:0] mem_addr,     // Input: Base memory address from ALU (rs + immediate offset)
    input  [31:0] mem_data,     // Input: Data read from external memory system
    input  [31:0] rf_rdata2,    // Input: Data from register rt (source for Stores, merge for LWL/R)
    output [31:0] load_data,    // Output: Processed data for Load instructions (to MemToReg)
    output [31:0] mem_addr_o,   // Output: Word-aligned memory address sent to memory system
    output [31:0] mem_wdata,    // Output: Data to write to memory system (for Store instructions)
    output [ 3:0] mem_strb      // Output: Byte strobes for memory write operations
);

  //----------------------------------------------------------------------------
  // Opcode Based Flags: Load and Store Detection
  //----------------------------------------------------------------------------
  // is_load: Flag indicating a Load instruction (opcode group 100xxx)
  wire is_load  = (opcode[5:3] == 3'b100);
  // is_store: Flag indicating a Store instruction (opcode group 101xxx)
  wire is_store = (opcode[5:3] == 3'b101);

  //----------------------------------------------------------------------------
  // Address Alignment and Byte Offset Calculation
  //----------------------------------------------------------------------------
  // addr_offset: Extract byte offset within the word from the memory address (bits [1:0])
  wire [1:0] addr_offset = mem_addr[1:0];
  // Individual byte address offset flags (for easier logic below)
  wire addr_0 = (addr_offset == 2'b00); // Offset 0 within word (byte address ends in 00)
  wire addr_1 = (addr_offset == 2'b01); // Offset 1 within word (byte address ends in 01)
  wire addr_2 = (addr_offset == 2'b10); // Offset 2 within word (byte address ends in 10)
  wire addr_3 = (addr_offset == 2'b11); // Offset 3 within word (byte address ends in 11)

  // mem_addr_o: Word-aligned memory address output (bits [31:2] from mem_addr, bits [1:0] forced to 00)
  assign mem_addr_o = {mem_addr[31:2], 2'b00};

  //----------------------------------------------------------------------------
  // Byte Strobe Generation for Store Operations (mem_strb)
  //----------------------------------------------------------------------------
  // mem_strb: Byte strobes to enable writing to specific byte lanes in memory.
  // Generated based on opcode (store type: SB, SH, SW, SWL, SWR) and byte offset (addr_offset).
  assign mem_strb =
    (({4{opcode[1:0] == 2'b00}} & (        // Store Byte (SB) - Opcode bits [1:0] == 00
        (addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0010 : 0) | // Strobe for each byte lane based on offset
        (addr_2 ? 4'b0100 : 0) | (addr_3 ? 4'b1000 : 0)
    )) |
    ({4{opcode[1:0] == 2'b01}} & (         // Store Halfword (SH) - Opcode bits [1:0] == 01
        (addr_0 ? 4'b0011 : 0) | (addr_2 ? 4'b1100 : 0)  // Strobes for aligned halfword addresses (offset 0 or 2)
    )) |
    ({4{opcode[1:0] == 2'b11}} & (         // Store Word (SW) - Opcode bits [1:0] == 11
        addr_0 ? 4'b1111 : 4'b0000         // Strobe all bytes if word-aligned (offset 0)
    )) |
    ({4{opcode[2:0] == 3'b010}} & (        // Store Word Left (SWL) - Opcode bits [2:0] == 010
        (addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0011 : 0) | // Strobes for writing from MSB towards LSB
        (addr_2 ? 4'b0111 : 0) | (addr_3 ? 4'b1111 : 0)
    )) |
    ({4{opcode[2:0] == 3'b110}} & (        // Store Word Right (SWR) - Opcode bits [2:0] == 110
        (addr_0 ? 4'b1111 : 0) | (addr_1 ? 4'b1110 : 0) | // Strobes for writing from LSB towards MSB
        (addr_2 ? 4'b1100 : 0) | (addr_3 ? 4'b1000 : 0)
    ))) & {4{is_store}}; // Only activate strobes if it's a store operation (is_store flag)

  //----------------------------------------------------------------------------
  // Memory Write Data Formatting (mem_wdata) for Store Operations
  //----------------------------------------------------------------------------
  // mem_wdata: Data to be written to memory. Formatted based on store type and alignment.
  assign mem_wdata =
    (({32{opcode[1:0] == 2'b00}} & (        // Store Byte (SB) - Opcode bits [1:0] == 00
        {4{rf_rdata2[7:0]}}                 // Replicate lower byte of rt across all byte lanes
    )) |
    ({32{opcode[1:0] == 2'b01}} & (         // Store Halfword (SH) - Opcode bits [1:0] == 01
        {2{rf_rdata2[15:0]}}                // Replicate lower halfword of rt across halfword lanes
    )) |
    ({32{opcode[1:0] == 2'b11}} & (         // Store Word (SW) - Opcode bits [1:0] == 11
        rf_rdata2                           // Use the full 32-bit value from rt
    )) |
    ({32{opcode[2:0] == 3'b010}} & (        // Store Word Left (SWL) - Opcode bits [2:0] == 010
        (addr_0 ? {24'b0, rf_rdata2[31:24]} :           // Write most significant byte (MSB) if offset 0
         addr_1 ? {16'b0, rf_rdata2[31:16]} :           // Write upper 2 bytes if offset 1
         addr_2 ? { 8'b0, rf_rdata2[31: 8]} :           // Write upper 3 bytes if offset 2
                  rf_rdata2)                            // Write all 4 bytes if offset 3 (effectively aligned word write)
    )) |
    ({32{opcode[2:0] == 3'b110}} & (        // Store Word Right (SWR) - Opcode bits [2:0] == 110
        (addr_0 ? rf_rdata2 :                           // Write all 4 bytes if offset 0 (effectively aligned word write)
         addr_1 ? {rf_rdata2[23:0],  8'b0} :            // Write lower 3 bytes if offset 1
         addr_2 ? {rf_rdata2[15:0], 16'b0} :            // Write lower 2 bytes if offset 2
                  {rf_rdata2[ 7:0], 24'b0})             // Write least significant byte (LSB) if offset 3
    ))) & {32{is_store}};                   // Only format write data if it's a store operation (is_store flag)

  //----------------------------------------------------------------------------
  // Load Data Processing (load_data) for Load Operations
  //----------------------------------------------------------------------------
  // load_data: Processed data read from memory, based on load type and alignment.
  assign load_data =
    ((opcode[1:0] == 2'b00) ?  // Load Byte (LB, LBU) - Opcode bits [1:0] == 00
      (addr_0 ? {{24{(~opcode[2] & mem_data [ 7])}}, mem_data [ 7: 0]} :   // Byte 0, sign-extend if LB, zero-extend if LBU
       addr_1 ? {{24{(~opcode[2] & mem_data [15])}}, mem_data [15: 8]} :   // Byte 1, sign/zero-extend
       addr_2 ? {{24{(~opcode[2] & mem_data [23])}}, mem_data [23:16]} :   // Byte 2, sign/zero-extend
                {{24{(~opcode[2] & mem_data [31])}}, mem_data [31:24]} ) : // Byte 3, sign/zero-extend

    ((opcode[1:0] == 2'b01) ?                 // Load Halfword (LH, LHU) - Opcode bits [1:0] == 01
       (addr_0 ? {{16{(~opcode[2] & mem_data [15])}}, mem_data [15: 0]} :  // Halfword 0 (bytes 0-1), sign-extend if LH, zero-extend if LHU
       addr_2 ? {{16{(~opcode[2] & mem_data [31])}}, mem_data [31:16]} :   // Halfword 1 (bytes 2-3), sign/zero-extend
                32'b0 ) :                     // Should not happen for aligned halfword load at offsets 1 or 3, but default to 0

    ((opcode[1:0] == 2'b11) ? mem_data :      // Load Word (LW) - Opcode bits [1:0] == 11, aligned word load
    ((opcode[2:0] == 3'b010) ?                // Load Word Left (LWL) - Opcode bits [2:0] == 010
       (addr_0 ? {mem_data [ 7: 0], rf_rdata2 [23: 0]} :  // Merge byte 0 from memory with upper 3 bytes from rt
       addr_1 ? {mem_data [15: 0], rf_rdata2 [15: 0]} :   // Merge bytes 0-1 from memory with upper 2 bytes from rt
       addr_2 ? {mem_data [23: 0], rf_rdata2 [ 7: 0]} :   // Merge bytes 0-2 from memory with upper byte from rt
                mem_data ) :                 // If offset 3, load entire word from memory (effectively LW)
    ((opcode[2:0] == 3'b110) ?               // Load Word Right (LWR) - Opcode bits [2:0] == 110
       (addr_0 ? mem_data :                  // If offset 0, load entire word from memory (effectively LW)
       addr_1 ? {rf_rdata2 [31:24], mem_data [31: 8]} :   // Merge upper byte from rt with bytes 1-3 from memory
       addr_2 ? {rf_rdata2 [31:16], mem_data [31:16]} :   // Merge upper 2 bytes from rt with lower 2 bytes from memory
                {rf_rdata2 [31: 8], mem_data [31:24]} ) : // Merge upper 3 bytes from rt with lower byte from memory
    32'b0))))) & {32{is_load}};              // Default case (should not be reached), and gate output with is_load flag

endmodule


//==============================================================================
// Module: move_and_load_imm_alu_controller
// Description: Detects and controls Move and Load Immediate instructions:
//              - Conditional Move: MOVZ (Move if Zero), MOVN (Move if Not Zero)
//              - Load Upper Immediate: LUI (Load Upper Immediate)
//              Provides control signals to other modules based on instruction type.
//==============================================================================
module move_and_load_imm_alu_controller (
    input  [ 5:0] opcode,      // Input: Instruction opcode
    input  [ 5:0] funct,       // Input: Instruction function field (for R-type)
    output        is_move,     // Output: Flag indicating MOVZ or MOVN instruction
    output        is_lui,      // Output: Flag indicating LUI instruction
    output [ 2:0] move_alu_op  // Output: ALU operation for MOVZ/MOVN (OR/ADD with zero)
);

  //----------------------------------------------------------------------------
  // Conditional Move Instruction Detection (MOVZ, MOVN)
  //----------------------------------------------------------------------------
  // is_move: Flag to indicate if the current instruction is MOVZ or MOVN (R-type).
  // MOVZ and MOVN are R-type instructions identified by specific funct field values.

  // --- Original Implementation (using named wires for clarity) ---
  /*
  wire movn = (~|opcode && funct == 6'b001011); // Move if Not Zero (rt != 0) - funct code 001011
  wire movz = (~|opcode && funct == 6'b001010); // Move if Zero (rt == 0)     - funct code 001010
  assign is_move = movn || movz;
  */

  // --- Optimized Implementation (direct logic formula based on funct bits) ---
  // Formula Breakdown:
  // - ~|opcode:  Ensures it's an R-type instruction (opcode is all zeros).
  // - funct[1]:  Funct bit 1 is common to both MOVZ and MOVN (funct[1] == 1).
  // - funct[3]:  Funct bit 3 is common to both MOVZ and MOVN (funct[3] == 1).
  // - !funct[5]: Funct bit 5 is 0 for both MOVZ and MOVN (funct[5] == 0).
  assign is_move = (~|opcode && funct[1] && funct[3] && !funct[5]);

  //----------------------------------------------------------------------------
  // ALU Operation for Conditional Moves (move_alu_op)
  //----------------------------------------------------------------------------
  // move_alu_op: Specifies the ALU operation to be performed for MOVZ/MOVN.
  // For MOVZ/MOVN, we need to effectively "move" the value of 'rs' to 'rd'
  // conditionally. This is achieved by using an ALU operation that simply passes
  // 'rs' through when combined with a zero operand.
  // Common choices are:
  // - OR with zero:  Result = 0 | rs = rs
  // - ADD with zero: Result = 0 + rs = rs
  // We choose OR operation (3'b001) here.

  assign move_alu_op = 3'b001; // OR operation (can also use ADD: 3'b010)

  //----------------------------------------------------------------------------
  // Load Upper Immediate Instruction Detection (LUI)
  //----------------------------------------------------------------------------
  // is_lui: Flag to indicate if the current instruction is LUI (Load Upper Immediate).
  // LUI is an I-type instruction with a specific opcode.
  // LUI opcode is 001111 (binary), which means bits [3:0] are all 1s.
  assign is_lui = (&opcode[3:0]); // Check if opcode[3:0] are all '1's (AND reduction)

endmodule


//==============================================================================
// Module: alu_src_selector
// Description: Selects the two source operands (alu_src1, alu_src2) for the ALU
//              based on the current instruction type and control signals.
//              Determines whether to use register values (rs, rt), immediate values
//              (imm_16, sign-extended or zero-extended), or special values (like 0 for branch compares).
//==============================================================================
module alu_src_selector (
    input  [ 5:0] opcode,             // Input: Instruction opcode
    input  [ 5:0] funct,              // Input: Instruction function field (for R-type instructions)
    input         alu_src_imm_input,  // Input: Control signal from Control Unit; selects immediate as ALU source 2
    input         is_branch_zero_cmp, // Input: Control signal; indicates branch instruction comparing rs against zero
    input         is_move,            // Input: Control signal; indicates MOVZ or MOVN instruction
    input  [15:0] imm_16,             // Input: 16-bit immediate value from the instruction
    input  [31:0] rs,                 // Input: Data read from register file for register 'rs'
    input  [31:0] rt,                 // Input: Data read from register file for register 'rt'
    output [31:0] alu_src1,           // Output: First operand for the ALU (Operand A)
    output [31:0] alu_src2            // Output: Second operand for the ALU (Operand B)
);

  //----------------------------------------------------------------------------
  // Immediate Value Extension
  //----------------------------------------------------------------------------
  // imm_SE: Sign-extended version of the 16-bit immediate value (imm_16) to 32 bits.
  wire [31:0] imm_SE = {{16{imm_16[15]}}, imm_16};
  // imm_0E: Zero-extended version of the 16-bit immediate value (imm_16) to 32 bits.
  wire [31:0] imm_0E = {16'b0, imm_16};

  //----------------------------------------------------------------------------
  // Zero-Extend Selection for Immediate Operand
  //----------------------------------------------------------------------------
  // use_zero_extend: Control signal to determine whether to use zero-extended or
  //                  sign-extended immediate value when immediate is selected as ALU source 2.
  // Zero extension is used for:
  // - ANDI (opcode 001100)
  // - ORI  (opcode 001101)
  // - XORI (opcode 001110)
  // Logic Formula: use_zero_extend = (!opcode[5] && opcode[2])
  wire use_zero_extend = (!opcode[5] && opcode[2]);

  //----------------------------------------------------------------------------
  // ALU Source 2 (Operand B) Selection Logic
  //----------------------------------------------------------------------------
  // Selects the second operand for the ALU (alu_src2) based on instruction type:
  // Priority is checked in the order listed below.
  assign alu_src2 =
    (is_branch_zero_cmp) ? 32'b0 :                 // 1. For branch instructions comparing against zero (BLEZ, BGTZ, etc.), use 0 as operand B.
    (alu_src_imm_input)  ?                         // 2. If alu_src_imm_input is asserted (Control Unit signals immediate operand):
      (use_zero_extend ? imm_0E : imm_SE) :        //    - Use zero-extended immediate (imm_0E) if use_zero_extend is true (ANDI, ORI, XORI).
                                                   //    - Otherwise, use sign-extended immediate (imm_SE).
    rt;                                            // 3. Default case: Use the value from register 'rt' as operand B.

  //----------------------------------------------------------------------------
  // ALU Source 1 (Operand A) Selection Logic
  //----------------------------------------------------------------------------
  // Selects the first operand for the ALU (alu_src1) based on instruction type:
  // Priority is checked in the order listed below.
  assign alu_src1 =
    (is_move) ? 32'b0 :                           // 1. For MOVZ/MOVN instructions, use 0 as operand A.
                                                  //    - ALU will perform OR operation (0 | rs) to effectively move 'rs' conditionally.
    rs;                                           // 2. Default case: Use the value from register 'rs' as operand A.

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
