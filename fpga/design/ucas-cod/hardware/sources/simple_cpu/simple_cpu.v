`timescale 10ns / 1ns

`define ADDR_WIDTH 5
`define DATA_WIDTH 32

module simple_cpu (
    input clk,
    input rst,

    output [31:0] PC,
    input  [31:0] Instruction,

    output [31:0] Address,
    output        MemWrite,
    output [31:0] Write_data,
    output [ 3:0] Write_strb,

    input  [31:0] Read_data,
    output        MemRead
);

  // THESE THREE SIGNALS ARE USED IN OUR TESTBENCH
  // PLEASE DO NOT MODIFY SIGNAL NAMES
  // AND PLEASE USE THEM TO CONNECT PORTS
  // OF YOUR INSTANTIATION OF THE REGISTER FILE MODULE
  wire RF_wen;
  wire [4:0] RF_waddr;
  wire [31:0] RF_wdata;

  // TODO: PLEASE ADD YOUR CODE BELOW
  wire [5:0] opcode = Instruction[31:26];  // opcode from instruction
  wire [4:0] rs = Instruction[25:21];  // rs from instruction
  wire [4:0] rt = Instruction[20:16];  // rt from instruction
  wire [4:0] rd = Instruction[15:11];  // rd from instruction
  wire [4:0] shamt = Instruction[10:6];  // shamt from instruction
  wire [5:0] funct = Instruction[5:0];  // funct from instruction, only used for r type
  wire [15:0] imm_16 = Instruction[15:0];  // immediate value from instruction

  wire [1:0] reg_dst_input;  // this is the output from control unit, and the input for reg_write_controller
  wire [1:0] is_jump_cond;  // this is the output from control unit, and the input for pc_controller
  wire is_branch;  // this is the output from control unit, and the input for pc_controller
  wire mem_read;  // this is the output from control unit, and the input for load_and_store_controller
  wire mem_write;  // this is the output from control unit, and the input for load_and_store_controller
  wire alu_src_imm_input;  // this is the output from control unit, and the input for alu_src_selector
  wire reg_write_cond;  // this is the output from control unit, and the input for reg_write_controller
  wire alu_op_ok;  // this is the output from control unit, and the input for arithmetic_controller and alu_op_generator
  wire [2:0] alu_op_cond;  // this is the output from control unit, and the input for arithmetic_controller and alu_op_generator

  control_unit instance_control_unit (
      .opcode(opcode),
      .reg_dst(reg_dst_input),
      .is_jump(is_jump_cond),
      .is_branch(is_branch),
      .mem_read(mem_read),
      .alu_op_cond(alu_op_cond),
      .alu_op_ok(alu_op_ok),
      .mem_write(mem_write),
      .alu_src_imm(alu_src_imm_input),
      .reg_write_cond(reg_write_cond)
  );

  wire [4:0] RF_waddr_final = RF_waddr;  // this is the final reg_dst to be sent to the register file
  wire reg_write_input;  // this is the input of the reg_write_signal_generator

  reg_write_controller instance_reg_write_controller (
      .opcode(opcode),
      .funct(funct),
      .rd(rd),
      .rt(rt),
      .input_reg_write_cond(reg_write_cond),
      .reg_dst_input(reg_dst_input),
      .reg_dst(RF_waddr),  // this is the final reg_dst to be sent to the register file
      .reg_write(reg_write_input)  // this is the input of the reg_write_signal_generator
  );

  wire is_shamt;  // this is the output from arithmetic_controller, to be used in shifter_src_selector
  wire [2:0] alu_op;  // this is the output from arithmetic_controller, to be sent to the alu_op_generator
  wire [1:0] shifter_op;  // this is the output from arithmetic_controller, to be sent to the shifter
  wire is_alu_operation;  // this is the output from arithmetic_controller, to be used in alu_src_selector
  wire is_shift_operation;  // this is the output from arithmetic_controller, to be used in shifter_src_selector

  arithmetic_controller instance_arithmetic_controller (
      .opcode(opcode),
      .funct(funct),
      .alu_op_input(alu_op_cond),  // this is the output from control unit
      .alu_op_ok(alu_op_ok),  // this is the output from control unit
      .is_shamt(is_shamt),  // use this signal with alu_src_imm, determine rt/imm/shamt
      .alu_op(alu_op),  // the final alu_op to be sent to the ALU
      .shifter_op(shifter_op),  // the shifter operation to be sent to the shifter
      .is_alu_operation(is_alu_operation),  // if it is an alu operation
      .is_shift_operation(is_shift_operation)  // if it is a shift operation
  );

  wire is_zero_cmp;  // this is the output from branch_controller, to be used in pc_controller

  branch_controller instance_branch_controller (
      .opcode(opcode),
      .funct(funct),
      .is_branch(is_branch),  // 1 means branch
      .is_zero_cmp(is_zero_cmp)  // if is_zero_cmp is 1, then we will compare rs with zero
  );

  wire [31:0] next_pc;  // the next pc to be sent to the PC module
  wire [31:0] pc_store;  // pc + 8, to be stored in the PC module
  wire [31:0] current_pc;  // current pc from the PC module
  wire is_jump; // this is the input of the mem_to_reg module, to determine if it is a jump instruction
  wire [31:0] RF_rdata1;  // this is the rs from register file, we will use this to determine
  // the next pc in jr instruction
  wire [31:0] RF_rdata2;  // this is the rt from register file, we will use this to determine
  // the next pc in load/store instruction
  wire [31:0] alu_result;  // this is the result from ALU, to be used in pc_controller
  wire alu_zero;  // this is the zero flag from ALU, to be used in pc_controller
  wire [31:0] shift_result;  // this is the result from shifter
  wire [31:0] alu_src1;  // this is the first operand for ALU
  wire [31:0] alu_src2;  // this is the second operand for ALU
  wire [2:0] alu_op_final;  // this is the final alu_op to be sent to the ALU
  wire [31:0] shifter_src1;  // this is the first operand for shifter
  wire [31:0] shifter_src2;  // this is the second operand for shifter


  pc_controller instance_pc_controller (
      .is_branch(is_branch),  // 1 means branch
      .current_pc(current_pc),  // current pc from the PC module
      .rs(RF_rdata1),  // this is the rs from register file, we will use this to determine
                       // the next pc in jr instruction
      .alu_result(alu_result),  // this is the result from ALU, we will use this to determine
                                // whether to branch or not
      .alu_zero(alu_zero),  // this is the zero flag from ALU, we will use this to determine
                            // whether to branch or not in beq instruction
      .instruction(Instruction),  // the instruction to be executed
      .is_jump(is_jump),  // if it is a jump instruction
      .next_pc(next_pc),  // the next pc to be sent to the PC module
      .pc_store(pc_store)  // pc + 8, to be stored in the PC module
  );

  pc instance_pc (
      .clk(clk),
      .rst(rst),
      .next_pc(next_pc),  // the next pc to be sent to the PC module
      .pc(current_pc)  // the current pc to be sent to the rest of the CPU
  );

  assign PC = current_pc;  // output the current pc to the top module
  wire [31:0] load_data;  // this is the data to be written to the register file

  load_and_store_controller instance_load_and_store_controller (
      .opcode(opcode),  // opcode from instruction
      .mem_addr(alu_result),  // result from alu, used as memory address
      .mem_data(Read_data),  // data read from memory
      .rf_rdata2(RF_rdata2),  // Data from second register for store and LWL/LWR
      .load_data(load_data),  // data to be written to the register file
      .mem_addr_o(Address),  // Memory address output
      .mem_wdata(Write_data),  // Memory write data output
      .mem_strb(Write_strb)  // Memory byte strobe output
  );

  wire is_move;
  wire is_lui;
  wire [2:0] move_alu_op;

  move_and_load_imm_alu_controller instance_move_and_load_imm_alu_controller (
      .opcode(opcode),  // opcode from instruction
      .funct(funct),  // funct from instruction, only used when opcode is 0
      .is_move(is_move),  // if it is a move instruction
      .is_lui(is_lui),  // if it is a lui instruction
      .move_alu_op(move_alu_op)  // the alu operation for move instruction
  );

  reg_write_signal_generator instance_reg_write_signal_generator (
      .reg_write_input(reg_write_input),
      .opcode(opcode),
      .funct(funct),
      .is_zero(alu_zero),
      .wen(RF_wen)
  );

  reg_file instance_reg_file (
      .clk(clk),
      .waddr(RF_waddr),
      .raddr1(rs),
      .raddr2(rt),
      .wen(RF_wen),
      .wdata(RF_wdata),
      .rdata1(RF_rdata1),
      .rdata2(RF_rdata2)
  );

  alu instance_alu (
      .A(alu_src1),
      .B(alu_src2),
      .ALUop(alu_op_final),
      .Overflow(),  // not used
      .CarryOut(),  // not used
      .Zero(alu_zero),
      .Result(alu_result)
  );

  shifter instance_shifter (
      .A(shifter_src1),
      .B(shifter_src2[4:0]),  // Apply pruning here to match expected width
      .Shiftop(shifter_op),
      .Result(shift_result)
  );

  alu_src_selector instance_alu_src_selector (
      .opcode(opcode),
      .funct(funct),
      .alu_src_imm_input(alu_src_imm_input),
      .is_branch(is_branch),
      .is_branch_zero_cmp(is_zero_cmp),
      .imm_16(imm_16),
      .rs(RF_rdata1),
      .rt(RF_rdata2),
      .alu_src1(alu_src1),
      .alu_src2(alu_src2)
  );

  shifter_src_selector instance_shifter_src_selector (
      .rs(RF_rdata1),
      .rt(RF_rdata2),
      .shamt(shamt),
      .is_shamt(is_shamt),
      .shifter_src1(shifter_src1),
      .shifter_src2(shifter_src2)
  );

  alu_op_generator instance_alu_op_generator (
      .alu_op_cond(alu_op_cond),
      .alu_op_ok(alu_op_ok),
      .alu_op(alu_op),
      .is_alu_operation(is_alu_operation),
      .is_move(is_move),
      .move_alu_op(move_alu_op),
      .alu_op_final(alu_op_final)
  );

  mem_to_reg instance_mem_to_reg (
      .is_alu_operation(is_alu_operation),
      .is_shift_operation(is_shift_operation),
      .memread(mem_read),
      .is_jump(is_jump),
      .is_lui(is_lui),
      .is_move(is_move),
      .alu_result(alu_result),
      .shift_result(shift_result),
      .mem_data(load_data),
      .pc_store(pc_store),
      .imm_16(imm_16),
      .rs(RF_rdata1),
      .write_data(RF_wdata)
  );

  assign MemWrite = mem_write;
  assign MemRead = mem_read;
  assign Write_data = Write_data; // Use RF_wdata as Write_data, as it's the data to be written to memory in store instructions
  assign Write_strb = Write_strb;  // From load_and_store_controller, already connected
  assign Address = Address;  // From load_and_store_controller, already connected

endmodule

module control_unit (
    input [5:0] opcode,
    output [1:0] reg_dst,
    output [1:0] is_jump,  // 0 means not jump, 1 means jump, 2 means jump and link
    output is_branch,
    output mem_read,
    output [2:0] alu_op_cond, // aluop could be decoded from opcode if it is an imm_arithmetic, branch, or load/store instruction
    output alu_op_ok, // if alu_op_ok is 1, then the alu_op is valid, otherwise, cannot obtain aluop from opcode
    output mem_write,
    output alu_src_imm, // this signal is 1 if alu_src is immediate, 0 if alu_src is register or shamt or ..., need to use with other conditions
    output reg_write_cond // this is the precondition of the wen signal for the register file, do not handle the following situations: b type, j type, movn, movz; need to use & with other conditions
);
  assign reg_dst = (opcode == 6'b000000) ? 2'b11 :
                 (opcode == 6'b000010 || opcode == 6'b000011) ? 2'b10 :
                 2'b01; // choose rt when others (including r type with funct 0)
  assign is_branch = (opcode[5:2] == 4'b0001 || opcode == 6'b000001) ? 1'b1 : 1'b0;
  assign mem_read = (opcode[5:3] == 3'b100) ? 1'b1 : 1'b0;
  assign mem_write = (opcode[5:3] == 3'b101) ? 1'b1 : 1'b0;
  assign reg_write_cond = (opcode[5:3] != 3'b101 && !is_branch) ? 1'b1 : 1'b0;
  assign alu_src_imm = (opcode[5:3] == 3'b001 || opcode[5:3] == 3'b100 || opcode[5:3] == 3'b101) ? 1'b1 : 1'b0;
  assign is_jump = (opcode == 6'b000010) ? 2'b01 :
                  (opcode == 6'b000011) ? 2'b10 :
                  2'b00; // not jump

  wire imm_arithmetic = (opcode[5:3] == 3'b001 && opcode[2:0] != 3'b111) ? 1'b1 : 1'b0; // does not include the lui instruction
  wire is_load_store = (opcode[5:3] == 3'b100 || opcode[5:3] == 3'b101) ? 1'b1 : 1'b0;
  wire addiu = (opcode[2:0] == 3'b001) ? 1'b1 : 1'b0;
  wire andi = (opcode[2:0] == 3'b100) ? 1'b1 : 1'b0;
  wire ori = (opcode[2:0] == 3'b101) ? 1'b1 : 1'b0;
  wire xori = (opcode[2:0] == 3'b110) ? 1'b1 : 1'b0;
  wire slti = (opcode[2:0] == 3'b010) ? 1'b1 : 1'b0;
  wire sltiu = (opcode[2:0] == 3'b011) ? 1'b1 : 1'b0;

  wire [2:0] arith_type = addiu ? 3'b010 :
                    andi ? 3'b000 :
                    ori ? 3'b001 :
                    xori ? 3'b100 :
                    slti ? 3'b111 :
                    sltiu ? 3'b011 :
                    3'b000;

  assign alu_op_cond = is_branch ? 3'b111 :
                      is_load_store ? 3'b010 :
                      imm_arithmetic ? arith_type :
                      3'b000; // r type

  assign alu_op_ok = (imm_arithmetic || is_branch || is_load_store) ? 1'b1 : 1'b0;
endmodule

module reg_write_controller (
    input [5:0] opcode,  // opcode from instruction
    input [5:0] funct,  // funct from instruction, only used when opcode is 0
    input [4:0] rd,  // rd from instruction, only used for r type
    input [4:0] rt,  // rt from instruction, only used for non-r type
    input input_reg_write_cond,
    input [1:0] reg_dst_input,  // this is the output from control unit, which is already processed
    output [4:0] reg_dst,  // this is the final reg_dst to be sent to the register file,
                           // but still does not include the movn and movz
                           // instructions
                           // 11 for rd, 10 for ra, 01 for rt, 00 for not used
    output reg_write  // this is the final reg_write to be sent to the register file,
                      // but still does not include the movn and movz instructions
);
  wire j = (opcode == 6'b000010) ? 1'b1 : 1'b0;  // jump instruction
  wire jal = (opcode == 6'b000011) ? 1'b1 : 1'b0;  // jump and link instruction
  wire jr = (opcode == 6'b000000 && funct == 6'b001000) ? 1'b1 : 1'b0;  // jump register instruction
  assign reg_write = (input_reg_write_cond && !j && !jr) ? 1'b1 : 1'b0; // only when we can write to the register file
  wire _reg_dst = {2{reg_write}} & reg_dst_input;  // if reg_write is 1, then we can use
  // reg_dst_input, otherwise, we will not use it
  assign reg_dst = (_reg_dst == 2'b11) ? rd :  // if reg_dst is 11, we will use rd
      (_reg_dst == 2'b10) ? 5'b11111 :  // if reg_dst is 10, we will use ra (31)
      (_reg_dst == 2'b01) ? rt :  // if reg_dst is 01, we will use rt
      5'b0;  // if reg_dst is 00, we will not use any register
endmodule

module arithmetic_controller (
    input [5:0] opcode,  // opcode from instruction
    input [5:0] funct,  // funct from instruction, only used when opcode is 0
    input [2:0] alu_op_input,
    input alu_op_ok,
    output is_shamt,  // use this signal with alu_src_imm, determine rt/imm/shamt
    output [2:0] alu_op,  // the final alu_op to be s ent to the ALU
    output [1:0] shifter_op,
    output is_alu_operation,
    output is_shift_operation
);

  assign is_alu_operation = ((opcode == 6'b000000 && funct[5] == 1'b1)
                          || (opcode[5:3] == 3'b001 && opcode[2:0] != 3'b111))
                          ? 1'b1 : 1'b0; // only r type and imm_arithmetic (except lui) can be alu operation

  assign is_shift_operation = (opcode == 6'b000000 && funct[5:3] == 3'b000)
                            ? 1'b1 : 1'b0; // only r type with sll, srl, sra can be shift operation

  wire addu = (funct[2:0] == 3'b001) ? 1'b1 : 1'b0;
  wire subu = (funct[2:0] == 3'b011) ? 1'b1 : 1'b0;
  wire _and = (funct[2:0] == 3'b100) ? 1'b1 : 1'b0;
  wire _nor = (funct[2:0] == 3'b111) ? 1'b1 : 1'b0;
  wire _or = (funct[2:0] == 3'b101) ? 1'b1 : 1'b0;
  wire _xor = (funct[2:0] == 3'b110) ? 1'b1 : 1'b0;
  wire slt = (funct[2:0] == 3'b010) ? 1'b1 : 1'b0;
  wire sltu = (funct[2:0] == 3'b011) ? 1'b1 : 1'b0;

  wire arith_type = addu ? 3'b010 :
                    subu ? 3'b110 :
                    _and ? 3'b000 :
                    _nor ? 3'b101 :
                    _or ? 3'b001 :
                    _xor ? 3'b100 :
                    slt ? 3'b111 :
                    sltu ? 3'b011 :
                    3'b000;

  assign alu_op = is_alu_operation
                ? (alu_op_ok ? alu_op_input : arith_type) : 3'b000; // default to 0 if not an alu operation

  wire sll = (funct[2:0] == 3'b000) ? 1'b1 : 1'b0;  // shift left logical
  wire sra = (funct[2:0] == 3'b011) ? 1'b1 : 1'b0;  // shift right arithmetic
  wire srl = (funct[2:0] == 3'b010) ? 1'b1 : 1'b0;  // shift right logical
  wire sllv = (funct[2:0] == 3'b100) ? 1'b1 : 1'b0;  // shift left logical variable
  wire srav = (funct[2:0] == 3'b111) ? 1'b1 : 1'b0;  // shift right arithmetic variable
  wire srlv = (funct[2:0] == 3'b110) ? 1'b1 : 1'b0;  // shift right logical variable

  wire shift_type = sll ? 2'b00 :
                    sra ? 2'b11 :
                    srl ? 2'b10 :
                    sllv ? 2'b00 :
                    srav ? 2'b11 :
                    srlv ? 2'b10 :
                    2'b00; // no shift

  assign shifter_op = is_shift_operation
                    ? shift_type : 2'b00; // default to no shift if not a shift operation

  assign is_shamt = (is_shift_operation && (sll || srl || sra))
                  ? 1'b1 : 1'b0; // only these three operations use shamt

endmodule

module branch_controller (
    input [5:0] opcode,  // opcode from instruction
    input [5:0] funct,  // funct from instruction
    input is_branch,  // 1 means branch
    output is_zero_cmp  // if is_zero_cmp is 1, then we will compare rs with zero
                        // to determine whether to branch or not
);
  assign is_zero_cmp = is_branch && (opcode == 6'b000001 || opcode == 6'b000110 || opcode == 6'b000111)
                      ? 1'b1 : 1'b0; // only blez, bgtz, bltz, bgez can be zero cmp
endmodule

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
                             (blez && (alu_result == 1 || alu_zero == 1)) ||
                             (bgtz && (alu_result == 0 || alu_zero != 1)) ||
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

module pc (
    input clk,
    input rst,
    input [31:0] next_pc,  // the next pc to be sent to the PC module
    output reg [31:0] pc  // the current pc to be sent to the rest of the CPU
);
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      pc <= 32'b0;  // reset the PC to 0
    end else begin
      pc <= next_pc;  // update the PC to the next_pc
    end
  end
endmodule

module load_and_store_controller (
    input  [ 5:0] opcode,      // opcode from instruction
    input  [31:0] mem_addr,    // result from alu
    input  [31:0] mem_data,    // data read from memory
    input  [31:0] rf_rdata2,   // Data from second register for store and LWL/LWR
    output [31:0] load_data,   // data to be written to the register file
    output [31:0] mem_addr_o,  // Memory address output
    output [31:0] mem_wdata,   // Memory write data output
    output [ 3:0] mem_strb     // Memory byte strobe output
);
  // Load instruction opcodes
  wire lb = (opcode == 6'b100000);  // load byte
  wire lbu = (opcode == 6'b100100);  // load byte unsigned
  wire lh = (opcode == 6'b100001);  // load halfword
  wire lhu = (opcode == 6'b100101);  // load halfword unsigned
  wire lw = (opcode == 6'b100011);  // load word
  wire lwl = (opcode == 6'b100010);  // load word left
  wire lwr = (opcode == 6'b100110);  // load word right

  // Store instruction opcodes
  wire sb = (opcode == 6'b101000);  // store byte
  wire sh = (opcode == 6'b101001);  // store halfword
  wire sw = (opcode == 6'b101011);  // store word
  wire swl = (opcode == 6'b101010);  // store word left
  wire swr = (opcode == 6'b101110);  // store word right


  wire type_load = lb | lbu | lh | lhu | lw | lwl | lwr;
  wire type_store = sb | sh | sw | swl | swr;
  wire type_mem_b = lb | lbu | sb;
  wire type_mem_h = lh | lhu | sh;
  wire type_mem_w = lw | sw;
  wire type_mem_wl = lwl | swl;
  wire type_mem_wr = lwr | swr;

  wire [1:0] addr_offset = mem_addr[1:0];
  wire addr_0 = (addr_offset == 2'b00);
  wire addr_1 = (addr_offset == 2'b01);
  wire addr_2 = (addr_offset == 2'b10);
  wire addr_3 = (addr_offset == 2'b11);

  // Define masks (使用wire定义，并直接赋值)
  wire mask_byte1 = 4'b0001;
  wire mask_byte2 = 4'b0010;
  wire mask_byte3 = 4'b0100;
  wire mask_byte4 = 4'b1000;
  wire mask_high2 = 4'b1100;
  wire mask_low2 = 4'b0011;
  wire mask_high3 = 4'b1110;
  wire mask_low3 = 4'b0111;
  wire mask_full = 4'b1111;

  // Memory Operations Assignments (根据提供的代码片段实现)
  assign mem_addr_o = {mem_addr[31:2], 2'b0};  // 地址计算保持一致，word 对齐
  assign mem_wdata = ({32{type_mem_b || type_mem_wr}} & {4{rf_rdata2[7:0]}}) |  // sb, swr
      ({32{type_mem_h}} & {2{rf_rdata2[15:0]}}) |  // sh
      ({32{type_mem_w}} & rf_rdata2) |  // sw
      ({32{type_mem_wl}} &  // swl
      (   {32{addr_0}} & {24'b0, rf_rdata2[31:24]}
                             | {32{addr_1}} & {16'b0, rf_rdata2[31:16]}
                             | {32{addr_2}} & { 8'b0, rf_rdata2[31: 8]}
                             | {32{addr_3}} & {       rf_rdata2[31: 0]}
                           )
                        );

  assign mem_strb = ({4{type_mem_b}} &  // sb
      (   {4{addr_0}} & mask_byte1
                             | {4{addr_1}} & mask_byte2
                             | {4{addr_2}} & mask_byte3
                             | {4{addr_3}} & mask_byte4
                           )
                        ) |
                        ({4{type_mem_h}} &                                    // sh
      ({4{addr_0}} & mask_low2 | {4{addr_2}} & mask_high2)) | ({4{type_mem_w}} & mask_full) |  // sw
      ({4{type_mem_wl}} &  // swl
      (   {4{addr_0}} & mask_byte1
                             | {4{addr_1}} & mask_low2
                             | {4{addr_2}} & mask_low3
                             | {4{addr_3}} & mask_full
                           )
                        ) |
                        ({4{type_mem_wr}} &                                   // swr
      (   {4{addr_0}} & mask_full
                             | {4{addr_1}} & mask_high3
                             | {4{addr_2}} & mask_high2
                             | {4{addr_3}} & mask_byte4
                           )
                        );


  assign load_data = (lb | lbu) ?  // Load Byte (Signed or Unsigned) (Load 部分保持不变)
      (addr_0 ? {{24{(lb & mem_data [ 7])}}, mem_data [ 7: 0]} :
       addr_1 ? {{24{(lb & mem_data [15])}}, mem_data [15: 8]} :
       addr_2 ? {{24{(lb & mem_data [23])}}, mem_data [23:16]} :
                {{24{(lb & mem_data [31])}}, mem_data [31:24]} ) :

    (lh | lhu) ?  // Load Halfword (Signed or Unsigned)
      (addr_0 ? {{16{(lh & mem_data [15])}}, mem_data [15: 0]} :
       addr_2 ? {{16{(lh & mem_data [31])}}, mem_data [31:16]} :
                32'bx ) : // Should not happen for properly aligned halfword load

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
    32'bx; // Default case, should not be reached

endmodule

module move_and_load_imm_alu_controller (
    input [5:0] opcode,  // opcode from instruction
    input [5:0] funct,  // funct from instruction, only used when opcode is 0
    output is_move,  // if it is a move instruction
    output is_lui,
    output [2:0] move_alu_op  // the alu operation for move instruction
);
  wire movn = (opcode == 6'b000000 && funct == 6'b001011) ? 1'b1 : 1'b0;  // move if not zero
  wire movz = (opcode == 6'b000000 && funct == 6'b001010) ? 1'b1 : 1'b0;  // move if zero
  assign is_move = movn || movz;  // if it is a move instruction
  assign move_alu_op = (is_move) ? 3'b001 : 3'b000;

  wire lui = (opcode == 6'b001111) ? 1'b1 : 1'b0;  // load upper immediate
  assign is_lui = lui;  // if it is a lui instruction
endmodule

module reg_write_signal_generator (
    input reg_write_input,
    input [5:0] opcode,
    input [5:0] funct,
    input is_zero,  // this is the zero flag from ALU, used for movn and movz
    output wen  // write enable signal for the register file
);
  wire movn = (opcode == 6'b000000 && funct == 6'b001011) ? 1'b1 : 1'b0;  // move if not zero
  wire movz = (opcode == 6'b000000 && funct == 6'b001010) ? 1'b1 : 1'b0;  // move if zero

  // wen is true if we can write to the register file
  assign wen = reg_write_input && !movn && !movz ? 1'b1 :
              (movn && !is_zero) ? 1'b1 :
              (movz && is_zero) ? 1'b1 :
              1'b0; // only when we can write to the register file
endmodule

module alu_src_selector (
    input [5:0] opcode,  // opcode from instruction
    input [5:0] funct,
    input alu_src_imm_input,  // this is the output from control unit
    input is_branch,
    input is_branch_zero_cmp,
    input [15:0] imm_16,  // immediate value from instruction, only used for arithmetic and branch instructions
    input [31:0] rs,
    input [31:0] rt,  // this is the rt from register file
    output [31:0] alu_src1,
    output [31:0] alu_src2  // this is the second operand for ALU
);
  wire imm_SE = {{16{imm_16[15]}}, imm_16};  // sign extend the immediate value
  wire imm_0E = {16'b0, imm_16};  // zero extend the immediate value
  wire andi = (opcode == 6'b001100) ? 1'b1 : 1'b0;  // andi instruction
  wire ori = (opcode == 6'b001101) ? 1'b1 : 1'b0;  // ori instruction
  wire xori = (opcode == 6'b001110) ? 1'b1 : 1'b0;  // xori instruction
  wire zero_extend = andi || ori || xori;  // if it is an immediate logical operation

  assign alu_src2 = (is_branch && is_branch_zero_cmp) ? 32'b0 :
                  (alu_src_imm_input) ?
                  (
                  zero_extend ? imm_0E : imm_SE
                  ) :
                  rt;

  wire movn = (opcode == 6'b000000 && funct == 6'b001011) ? 1'b1 : 1'b0;  // move if not zero
  wire movz = (opcode == 6'b000000 && funct == 6'b001010) ? 1'b1 : 1'b0;  // move if zero
  wire is_move = movn || movz;  // if it is a move instruction

  assign alu_src1 = (is_move) ? 32'b0 : rs;  // if it is a move instruction, we will use 0 as the first operand

endmodule

module shifter_src_selector (
    input [31:0] rs,
    input [31:0] rt,
    input [4:0] shamt,  // shift amount, only used for sll, srl, sra
    input is_shamt,  // use this signal to determine if we are using shamt
    output [31:0] shifter_src1,  // this is the first operand for shifter
    output [31:0] shifter_src2  // this is the second operand for shifter
);
  assign shifter_src1 = rt;
  assign shifter_src2 = (is_shamt) ? shamt :
                      {{27{1'b0}}, rs[4:0]};  // if we are using shamt, we will use it as the second operand, otherwise, we will use rs
endmodule

module alu_op_generator (
    input [2:0] alu_op_cond,  // this is the output from control unit
    input alu_op_ok,  // this is the output from control unit, determine if we can use alu_op_cond
    input [2:0] alu_op,  // signal generated by arithmetic_controller
    input is_alu_operation,  // determine whether the signal above is valid
    input is_move,  // if it is a move instruction
    input [2:0] move_alu_op,  // the alu operation for move instruction
    output [2:0] alu_op_final  // the final alu operation to be sent to the ALU
);
  assign alu_op_final = (is_move) ? move_alu_op :
                      (is_alu_operation) ? alu_op :
                      (alu_op_ok) ? alu_op_cond :
                      3'b0;
endmodule

module mem_to_reg (
    input is_alu_operation,  // whether it is an ALU operation
    input is_shift_operation,  // whether it is a shift operation
    input memread,  // if we are reading from memory
    input is_jump,  // if it is a jump instruction
    input is_lui,  // if it is a lui instruction
    input is_move,  // if it is a move instruction
    input [31:0] alu_result,  // result from ALU
    input [31:0] shift_result,  // result from shifter, only used for shift operation
    input [31:0] mem_data,  // data from memory or load instruction
    input [31:0] pc_store,  // pc + 8, to be stored in the PC module
    input [15:0] imm_16,  // immediate value from instruction, only used for lui
    input [31:0] rs,  // rs from register file, only used for move instruction
    output [31:0] write_data  // data to be written to the register file
);
  wire imm_modified = {imm_16, {16{1'b0}}};
  assign write_data = (is_alu_operation) ? alu_result :
                      (is_shift_operation) ? shift_result :
                      (memread) ? mem_data :
                      (is_jump) ? pc_store :
                      (is_lui) ? imm_modified :
                      (is_move) ? rs :
                      32'b0;  // default to 0 if none of the above conditions are met
endmodule

