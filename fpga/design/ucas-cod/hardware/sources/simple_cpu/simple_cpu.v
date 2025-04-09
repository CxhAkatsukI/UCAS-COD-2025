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
    input         clk,            // Clock signal
    input         rst,            // Reset signal

    //-- Instruction Fetch Interface --
    output [31:0] PC,             // Program Counter output
    input  [31:0] Instruction,    // Instruction input from memory

    //-- Data Memory Interface --
    output [31:0] Address,        // Memory address output
    output        MemWrite,       // Memory write enable signal
    output [31:0] Write_data,     // Data to write to memory
    output [ 3:0] Write_strb,     // Memory byte strobes for writes
    input  [31:0] Read_data,      // Data read from memory
    output        MemRead         // Memory read enable signal
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
  wire [15:0] imm_16   = Instruction[15: 0]; // 16-bit immediate value
  wire [25:0] imm_J    = Instruction[25: 0]; // 26-bit immediate for jump

  //----------------------------------------------------------------------------
  // Internal Wires - Connecting Logic Blocks and Modules
  //----------------------------------------------------------------------------

  //-- Signals from Control Logic (ex-control_unit) --
  wire        reg_dst_input;          // Selects destination register (rd/rt/ra hint)
  wire        is_branch;              // Indicates Branch instruction
  wire        mem_read_internal;      // Internal Memory read enable (Load)
  wire        mem_write_internal;     // Internal Memory write enable (Store)
  wire        alu_src_imm_input;      // Selects ALU source 2 (Reg/Imm)
  wire        reg_write_cond;         // Precondition for register write enable
  wire        alu_op_ok;              // Indicates ALUOp can be derived from opcode
  wire [ 2:0] alu_op_cond;            // ALU operation hint from opcode

  //-- Signals for Register File Interface --
  wire        RF_wen;                 // Final write enable to RegFile
  wire [ 4:0] RF_waddr;               // Write address to RegFile
  wire [31:0] RF_wdata;               // Write data to RegFile
  wire [31:0] RF_rdata1;              // Data read from RegFile port 1 (rs)
  wire [31:0] RF_rdata2;              // Data read from RegFile port 2 (rt)

  //-- Signals for PC Control Path --
  wire [31:0] next_pc;                // Next program counter value
  wire [31:0] current_pc;             // Current program counter value (from PC module)
  wire [31:0] pc_store;               // PC+8 for JAL/JALR link address
  wire        is_jump;                // Indicates any Jump instruction occurred (J, JAL, JR, JALR)
  wire        is_link_jump;           // Indicates JAL or JALR instruction

  //-- Signals for ALU/Shifter Path --
  wire        is_shamt;               // Indicates shamt is used for shift amount
  wire [ 2:0] alu_op;                 // ALU operation for R-type/I-type Arithmetic
  wire [ 1:0] shifter_op;             // Shift operation type
  wire        is_alu_operation;       // Indicates an ALU operation is performed
  wire        is_shift_operation;     // Indicates a Shift operation is performed
  wire [31:0] alu_src1;               // First ALU operand
  wire [31:0] alu_src2;               // Second ALU operand
  wire [31:0] shifter_src1;           // First Shifter operand (data)
  wire [31:0] shifter_src2;           // Second Shifter operand (shift amount)
  wire [ 2:0] alu_op_final;           // Final ALU operation control to ALU
  wire [31:0] alu_result;             // ALU computation result
  wire        alu_zero;               // ALU Zero flag
  wire [31:0] shift_result;           // Shifter result

  //-- Signals for Branch Control Path --
  wire        is_zero_cmp;            // Indicates branch compares rs against zero

  //-- Signals for Load/Store Path --
  wire [31:0] load_data;              // Data processed from memory/registers for load operations

  //-- Signals for Move/LUI Path --
  wire        is_move;                // Indicates MOVZ/MOVN
  wire        is_lui;                 // Indicates LUI instruction
  wire [ 2:0] move_alu_op;            // ALU operation for MOVZ/MOVN

  //----------------------------------------------------------------------------
  // Instantiated Modules
  //----------------------------------------------------------------------------

  //-- STAGE 1: Instruction Fetch (IF) --
  pc instance_pc (
      .clk        (clk),
      .rst        (rst),
      .next_pc    (next_pc),          // Input: Next PC value from PC Controller Logic
      .pc         (current_pc)        // Output: Current PC value
  );

  //-- STAGE 2: Register Fetch (ID) --
  reg_file instance_reg_file (
      .clk        (clk),
      .waddr      (RF_waddr),         // Input: Write address from Reg Write Controller Logic
      .raddr1     (rs),               // Input: Read address 1 (rs field)
      .raddr2     (rt),               // Input: Read address 2 (rt field)
      .wen        (RF_wen),           // Input: Write enable from Reg Write Controller Logic
      .wdata      (RF_wdata),         // Input: Write data from MemToReg Logic
      .rdata1     (RF_rdata1),        // Output: Read data 1 (rs value)
      .rdata2     (RF_rdata2)         // Output: Read data 2 (rt value)
  );

  //-- STAGE 3: Execute (EX) --
  // Arithmetic Logic Unit
  alu instance_alu (
      .A          (alu_src1),         // Input: Operand 1 from ALU Source Selector Logic
      .B          (alu_src2),         // Input: Operand 2 from ALU Source Selector Logic
      .ALUop      (alu_op_final),     // Input: Final ALU operation code from ALU Op Generator Logic
      .Overflow   (),                 // Output: Overflow flag (unused)
      .CarryOut   (),                 // Output: Carry Out flag (unused)
      .Zero       (alu_zero),         // Output: Zero flag (result is zero)
      .Result     (alu_result)        // Output: ALU computation result
  );

  // Shifter Unit
  shifter instance_shifter (
      .A          (shifter_src1),         // Input: Data operand from Shifter Source Selector Logic
      .B          (shifter_src2[4:0]),    // Input: Shift amount [4:0] from Shifter Source Selector Logic
      .Shiftop    (shifter_op),           // Input: Shift operation type from Arithmetic Controller Logic
      .Result     (shift_result)          // Output: Shifter result
  );

  //----------------------------------------------------------------------------
  // Integrated Logic (Replaces instantiated modules)
  //----------------------------------------------------------------------------

  //-- Control Unit Logic --
  wire        is_branch_sub     = (opcode[5:2] == 4'b0001);
  wire        is_branch_slt     = (opcode == 6'b000001);
  assign      is_branch         = (is_branch_sub || is_branch_slt);
  assign      reg_dst_input     = opcode[5] ^ opcode[3];
  assign      mem_read_internal = (opcode[5:3] == 3'b100);
  assign      mem_write_internal= (opcode[5:3] == 3'b101);
  assign      reg_write_cond    = !mem_write_internal && !is_branch;
  assign      alu_src_imm_input = ((opcode[5] || opcode[3]) && !opcode[4]);

  wire        imm_arithmetic    = (opcode[5:3] == 3'b001 && ~&opcode[2:0]);
  wire        is_load_store     = mem_read_internal || mem_write_internal;
  wire [ 2:0] arith_type;
  assign      arith_type[0]     = (~opcode[2] & opcode[1]) | (opcode[2] & opcode[0]);
  assign      arith_type[1]     = ~opcode[2];
  assign      arith_type[2]     = opcode[1] & ~opcode[0];
  assign      alu_op_cond       = is_branch_slt  ? 3'b111 :
                                  is_branch_sub  ? 3'b110 :
                                  is_load_store  ? 3'b010 :
                                  imm_arithmetic ? arith_type :
                                  3'bxxx;
  assign      alu_op_ok         = (imm_arithmetic || is_branch || is_load_store);


  //-- Arithmetic Controller Logic --
  assign      is_alu_operation   = ((~|opcode && funct[5] == 1'b1) || imm_arithmetic);
  assign      is_shift_operation = (~|opcode && ~|funct[5:3]);

  wire [ 2:0] r_type_arith_op;
  assign      r_type_arith_op[0] = (funct[3] & funct[1]) | (~funct[3] & funct[2] & funct[0]);
  assign      r_type_arith_op[1] = funct[3] | ~funct[2];
  assign      r_type_arith_op[2] = (funct[3] & ~funct[0]) | (~funct[3] & funct[1]);
  assign      alu_op             = (~|opcode) ? r_type_arith_op : alu_op_cond ;

  wire [ 1:0] shift_type;
  assign      shift_type[0]      = funct[1] & funct[0];
  assign      shift_type[1]      = funct[1];
  assign      shifter_op         = is_shift_operation ? shift_type : 2'b00;
  assign      is_shamt           = is_shift_operation && ~funct[2];


  //-- Branch Controller Logic --
  assign      is_zero_cmp        = is_branch && (opcode[2:0] == 3'b110 || opcode[2:0] == 3'b111 || opcode[2:0] == 3'b001);


  //-- Move/LUI Controller Logic --
  assign      is_move            = (~|opcode && funct[1] && funct[3] && !funct[5]);
  assign      is_lui             = (opcode == 6'b001111);
  assign      move_alu_op        = 3'b001;


  //-- ALU Source Selector Logic --
  wire [31:0] imm_SE             = {{16{imm_16[15]}}, imm_16};
  wire [31:0] imm_0E             = {16'b0, imm_16};
  wire        use_zero_extend    = (opcode[5:3] == 3'b001) && opcode[2];
  assign      alu_src1           = (is_move) ? 32'b0 : RF_rdata1;
  assign      alu_src2           = (is_zero_cmp)       ? 32'b0 :
                                   (alu_src_imm_input) ? (use_zero_extend ? imm_0E : imm_SE) :
                                   RF_rdata2;


  //-- Shifter Source Selector Logic --
  assign      shifter_src1       = RF_rdata2;
  assign      shifter_src2       = (is_shamt) ? {27'b0, shamt} : {27'b0, RF_rdata1[4:0]};


  //-- ALU Op Generator Logic --
  assign      alu_op_final       = (is_move)          ? move_alu_op :
                                   (is_alu_operation) ? alu_op :
                                   (alu_op_ok)        ? alu_op_cond :
                                   3'b010;


  //-- PC Controller Logic --
  wire [ 4:0] funct_branch       = rt; // rt field used for REGIMM function code
  wire        branch_condition_satisfied;
  assign      branch_condition_satisfied = is_branch &&
                                           ( (is_branch_slt && (funct_branch[0] ^ alu_result[0])) ||
                                             (is_branch_sub && opcode[1] && (opcode[0] ^ (alu_result[31] || alu_zero))) ||
                                             (is_branch_sub && !opcode[1] && (opcode[0] ^ alu_zero))
                                           );

  wire [31:0] imm_B_ext          = {{16{imm_16[15]}}, imm_16};
  wire [31:0] branch_target      = (current_pc + 4) + (imm_B_ext << 2);

  wire        is_j_instr         = (opcode == 6'b000010);
  wire        is_jal_instr       = (opcode == 6'b000011);
  wire        is_jr_instr        = (~|opcode && funct == 6'b001000);
  wire        is_jalr_instr      = (~|opcode && funct == 6'b001001);
  assign      is_jump            = is_j_instr || is_jal_instr || is_jr_instr || is_jalr_instr;
  assign      is_link_jump       = is_jal_instr || is_jalr_instr;

  wire [31:0] jump_target        = (is_j_instr || is_jal_instr) ? {current_pc[31:28], imm_J, 2'b00} : RF_rdata1;

  assign      next_pc            = (rst)                             ? 32'h00000000 :
                                   (is_jump)                         ? jump_target :
                                   (is_branch && branch_condition_satisfied) ? branch_target :
                                   current_pc + 4;
  assign      pc_store           = is_link_jump ? (current_pc + 8) : 32'b0;


  //-- Load/Store Controller Logic --
  wire        is_load            = mem_read_internal;
  wire        is_store           = mem_write_internal;
  wire [ 1:0] addr_offset        = alu_result[1:0];
  wire        addr_0             = (addr_offset == 2'b00);
  wire        addr_1             = (addr_offset == 2'b01);
  wire        addr_2             = (addr_offset == 2'b10);
  wire        addr_3             = (addr_offset == 2'b11);

  assign      Address            = {alu_result[31:2], 2'b00};

  assign      Write_strb         = {4{is_store}} & (
                                     (({4{opcode[1:0] == 2'b00}} & ((addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0010 : 0) | (addr_2 ? 4'b0100 : 0) | (addr_3 ? 4'b1000 : 0))) | // SB
                                     ({4{opcode[1:0] == 2'b01}} & ((addr_0 ? 4'b0011 : 0) | (addr_2 ? 4'b1100 : 0))) | // SH
                                     ({4{opcode[1:0] == 2'b11}} & (addr_0 ? 4'b1111 : 4'b0000)) | // SW
                                     ({4{opcode[2:0] == 3'b010}} & ((addr_0 ? 4'b0001 : 0) | (addr_1 ? 4'b0011 : 0) | (addr_2 ? 4'b0111 : 0) | (addr_3 ? 4'b1111 : 0))) | // SWL
                                     ({4{opcode[2:0] == 3'b110}} & ((addr_0 ? 4'b1111 : 0) | (addr_1 ? 4'b1110 : 0) | (addr_2 ? 4'b1100 : 0) | (addr_3 ? 4'b1000 : 0)))  // SWR
                                    ));

  // Write_data for SWL/SWR kept as is per previous constraints (may need review for correctness)
  assign      Write_data         = {32{is_store}} & (
                                     (({32{opcode[1:0] == 2'b00}} & {4{RF_rdata2[7:0]}}) | // SB
                                     ({32{opcode[1:0] == 2'b01}} & {2{RF_rdata2[15:0]}}) | // SH
                                     ({32{opcode[1:0] == 2'b11}} & RF_rdata2) | // SW
                                     ({32{opcode[2:0] == 3'b010}} & ( // SWL
                                         (addr_0 ? {24'b0, RF_rdata2[31:24]} :
                                          addr_1 ? {16'b0, RF_rdata2[31:16]} :
                                          addr_2 ? { 8'b0, RF_rdata2[31: 8]} :
                                                   RF_rdata2)
                                     )) |
                                     ({32{opcode[2:0] == 3'b110}} & ( // SWR
                                         (addr_0 ? RF_rdata2 :
                                          addr_1 ? {RF_rdata2[23:0],  8'b0} :
                                          addr_2 ? {RF_rdata2[15:0], 16'b0} :
                                                   {RF_rdata2[ 7:0], 24'b0})
                                     )))
                                   );

   // Processed Load Data (input to MemToReg logic)
   assign      load_data          = is_load ?
                                    ( (opcode[1:0] == 2'b00) ?  // LB/LBU
                                      (addr_0 ? {{24{(~opcode[2] & Read_data [ 7])}}, Read_data [ 7: 0]} :
                                       addr_1 ? {{24{(~opcode[2] & Read_data [15])}}, Read_data [15: 8]} :
                                       addr_2 ? {{24{(~opcode[2] & Read_data [23])}}, Read_data [23:16]} :
                                                {{24{(~opcode[2] & Read_data [31])}}, Read_data [31:24]} )

                                    : (opcode[1:0] == 2'b01) ? // LH/LHU
                                      (addr_0 ? {{16{(~opcode[2] & Read_data [15])}}, Read_data [15: 0]} :
                                       addr_2 ? {{16{(~opcode[2] & Read_data [31])}}, Read_data [31:16]} :
                                                32'b0 )

                                    : (opcode[1:0] == 2'b11) ? Read_data // LW

                                    // --- Start of Restored LWL/LWR Logic ---
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
                                    // --- End of Restored LWL/LWR Logic ---

                                    : 32'b0 ) // Default unknown load
                                    : 32'b0; // Default if not a load


  //-- Register Write Controller Logic --
  wire        write_disallowed   = is_j_instr || is_jr_instr || is_store;
  wire        intermediate_reg_write_cond = reg_write_cond && !write_disallowed;
  assign      RF_waddr           = (is_link_jump) ? 5'd31 : (reg_dst_input) ? rt : rd;
  assign      RF_wen             = (intermediate_reg_write_cond && !is_move) ||
                                   (is_move && (funct[0] ^ alu_zero) && reg_write_cond);


  //-- MemToReg Logic --
  wire [31:0] lui_result         = {imm_16, 16'b0};
  assign      RF_wdata           = (is_lui)             ? lui_result :
                                   (is_load)            ? load_data :
                                   (is_move)            ? RF_rdata1 :
                                   (is_alu_operation)   ? alu_result :
                                   (is_shift_operation) ? shift_result :
                                   (is_link_jump)       ? pc_store :
                                   32'b0;


  //----------------------------------------------------------------------------
  // Top-Level Output Assignments
  //----------------------------------------------------------------------------
  assign      PC                 = current_pc;
  assign      MemWrite           = mem_write_internal;
  assign      MemRead            = mem_read_internal;

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
    output reg [31:0] pc      // Output: Address of the current instruction
);

  // Sequential logic for PC register
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      pc <= 32'h00000000; // Reset PC to 0
    end else begin
      pc <= next_pc;      // Update PC with the calculated next address
    end
  end

endmodule
