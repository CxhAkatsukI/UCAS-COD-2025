`timescale 10ns / 1ns

module custom_cpu (
    input             clk,
    input             rst,

    /* Instruction request channel */
    output reg [31:0] PC,
    output            Inst_Req_Valid,
    input             Inst_Req_Ready,

    /* Instruction response channel */
    input      [31:0] Instruction,
    input             Inst_Valid,
    output            Inst_Ready,

    /* Memory request channel */
    output     [31:0] Address,
    output            MemWrite,
    output     [31:0] Write_data,
    output     [ 3:0] Write_strb,
    output            MemRead,
    input             Mem_Req_Ready,

    /* Memory data response channel */
    input      [31:0] Read_data,
    input             Read_data_Valid,
    output            Read_data_Ready,

    input             intr,

    output     [31:0] cpu_perf_cnt_0,
    output     [31:0] cpu_perf_cnt_1,
    output     [31:0] cpu_perf_cnt_2,
    output     [31:0] cpu_perf_cnt_3,
    output     [31:0] cpu_perf_cnt_4,
    output     [31:0] cpu_perf_cnt_5,
    output     [31:0] cpu_perf_cnt_6,
    output     [31:0] cpu_perf_cnt_7,
    output     [31:0] cpu_perf_cnt_8,
    output     [31:0] cpu_perf_cnt_9,
    output     [31:0] cpu_perf_cnt_10,
    output     [31:0] cpu_perf_cnt_11,
    output     [31:0] cpu_perf_cnt_12,
    output     [31:0] cpu_perf_cnt_13,
    output     [31:0] cpu_perf_cnt_14,
    output     [31:0] cpu_perf_cnt_15,

    output     [69:0] inst_retire
);

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
    // wire       [69:0] inst_retire;


    /*
    ** {================================================================================
    ** Local Parameters
    ** =================================================================================
    */

    /* ALUop */
    localparam  AND  = 3'b000,
                OR   = 3'b001,
                XOR  = 3'b100,
                NOR  = 3'b101,
                ADD  = 3'b010,
                SUB  = 3'b110,
                SLT  = 3'b111,
                SLTU = 3'b011;

    /* mask */
    localparam  mask_byte1 = 4'b0001,
                mask_byte2 = 4'b0010,
                mask_byte3 = 4'b0100,
                mask_byte4 = 4'b1000,
                mask_high2 = 4'b1100,
                mask_low2  = 4'b0011,
                mask_high3 = 4'b1110,
                mask_low3  = 4'b0111,
                mask_full  = 4'b1111;

    /* State */
    localparam   INIT = 9'b000000001, /* Initialize */
                 IF   = 9'b000000010, /* Instruction Fetch, Reg_File Read */
                 IW   = 9'b000000100, /* Instruction Wait */
                 ID   = 9'b000001000, /* Instruction Decode */
                 EX   = 9'b000010000, /* Execution or Address Calculation */
                 ST   = 9'b000100000, /* Store */
                 LD   = 9'b001000000, /* Load */
                 RDW  = 9'b010000000, /* Read Data Read */
                 WB   = 9'b100000000; /* Write Back */

    /* }================================================================================ */



    /*
    ** {=======================================================================================================
    ** Wire Variables
    ** ========================================================================================================
    */

    /* next_state */
    wire [8:0] next_state;

    /* State */

    wire /* 001 */ state_INIT;
    wire /* 002 */ state_IF;
    wire /* 004 */ state_IW;
    wire /* 008 */ state_ID;
    wire /* 010 */ state_EX;
    wire /* 020 */ state_ST;
    wire /* 040 */ state_LD;
    wire /* 080 */ state_RDW;
    wire /* 100 */ state_WB;

    wire EX_or_WB;


    /* reg file */
    wire        RF_wen;
    wire [ 4:0] RF_waddr;
    wire [ 4:0] RF_raddr1;
    wire [ 4:0] RF_raddr2;
    wire [31:0] RF_wdata;
    wire [31:0] RF_rdata1;
    wire [31:0] RF_rdata2;

    /* fields in the instruction */
    wire [ 5:0] opcode, func;
    wire [ 4:0] rs, rt, rd, shamt;
    wire [15:0] imm;
    wire [25:0] tar;

    /* immediate or offset extended */
    wire [31:0] imm_ZE; /* zero extend */
    wire [31:0] imm_SE; /* sign extend */


    /*
     * types of different instructions
     */

    /* No Operation */
    wire type_NOP; // nop

    /* R-Type */
    wire type_R; // type_R_cal, type_R_shift, type_R_j, type_R_mov
    wire type_R_cal; // addu~sltu
    wire type_R_shift; // sll~srlv
    wire type_R_j; // jr, jalr
    wire type_R_mov; // movn, movz

    /* J-Type */
    wire type_J; // j, jal

    /* I-Type */
    wire type_I; // all except J & R
    wire type_I_cal; // addiu~sltiu, lui
    wire type_I_branch; // beq~bgtz
    wire type_I_load; // lb~lwr
    wire type_I_store; // sb~swr

    /* REGIMM */
    wire type_RI_branch; // bltz, bgez

    /* other combinations */
    wire type_branch; // beq~bgez
    wire type_i_b; // type_I_cal, type_branch
    wire type_jr_mov; // type_R_j, type_R_mov
    wire type_jal; // jal, jalr

    /* whether conditions of branch type instructions are met */
    wire branch_OK;

    /* instructions about memory reading and writing */
    wire type_mem_b; // lb, lbu, sb
    wire type_mem_h; // lh, lhu, sh
    wire type_mem_w; // lw, sw
    wire type_mem_wl; // lwl, swl
    wire type_mem_wr; // lwr, swr

    /* for reading data in memory */
    wire [31:0] R_data_mod;

    /* the least significant 2 bits of address */
    wire addr_00, addr_01, addr_10, addr_11;


    /* ALU ports */
    wire [ 2:0] ALUop;
    wire [31:0] alu_A, alu_B, alu_result;
    wire        Zero;

    /* shifter ports */
    wire [ 1:0] Shiftop;
    wire [31:0] shifter_A;
    wire [ 4:0] shifter_B;
    wire [31:0] shifter_result;

    /* }======================================================================================================= */



    /*
    ** {===========================================================================
    ** Registers
    ** ============================================================================
    */

    reg  [ 8:0] current_state; /* fot FSM */
    reg  [31:0] IR;            /* Instruction Register */
    reg  [31:0] MDR;           /* Memory Data Register */
    // reg  [31:0] tmp_A;      /* the temporary of A, unused if not pipeline */
    // reg  [31:0] tmp_B;      /* the temporary of B, unused if not pipeline */
    reg  [31:0] alu_out;       /* the temporary of alu_result */

    reg  [31:0] cycle_cnt;     /*  0: cycles          */
    reg  [31:0] ins_cnt;       /*  1: instructions    */
    reg  [31:0] nop_cnt;       /*  2: [nop]           */
    reg  [31:0] IW_cnt;        /*  3: IW delay        */
    reg  [31:0] ST_cnt;        /*  4: ST delay        */
    reg  [31:0] LD_RDW_cnt;    /*  5: LD_RDW delay    */
    reg  [31:0] RI_cnt;        /*  6: branch(REGIMM)  */
    reg  [31:0] I_b_cnt;       /*  7: branch(I-type)  */
    reg  [31:0] branch_cnt;    /*  8: branch          */
    reg  [31:0] branchOK_cnt;  /*  9: branch success  */
    reg  [31:0] jump_cnt;      /* 10: jump            */
    reg  [31:0] MemR_cnt;      /* 11: memory read     */
    reg  [31:0] MemW_cnt;      /* 12: memory write    */
    reg  [31:0] Memop_cnt;     /* 13: memory total    */
    reg  [31:0] movOK_cnt;     /* 14: mov success     */
    reg  [31:0] RFW_cnt;       /* 15: RF write        */

    /* }=========================================================================== */



    /*
    ** {==============================
    ** Instantiations Of Modules
    ** ===============================
    */

    /* instantiate ALU */
    alu alu_inst (
        .A(              alu_A),
        .B(              alu_B),
        .ALUop(          ALUop),
        .Zero(            Zero),
        .Result(    alu_result)
    );

    /* instantiate shifter */
    shifter shifter_inst (
        .A(          shifter_A),
        .B(          shifter_B),
        .Shiftop(      Shiftop),
        .Result(shifter_result)
    );

    /* instantiate reg_file */
    reg_file reg_file_inst (
        .clk(              clk),
        .waddr(       RF_waddr),
        .raddr1(     RF_raddr1),
        .raddr2(     RF_raddr2),
        .wen(           RF_wen),
        .wdata(       RF_wdata),
        .rdata1(     RF_rdata1),
        .rdata2(     RF_rdata2)
    );

    /* }============================== */



    /*
    ** {===========================================================================================================================
    ** Definitions Of Wire Variables
    ** ============================================================================================================================
    */

    /* define state */
    assign  state_INIT = (current_state == INIT);
    assign  state_IF   = (current_state == IF);
    assign  state_IW   = (current_state == IW);
    assign  state_ID   = (current_state == ID);
    assign  state_EX   = (current_state == EX);
    assign  state_ST   = (current_state == ST);
    assign  state_LD   = (current_state == LD);
    assign  state_RDW  = (current_state == RDW);
    assign  state_WB   = (current_state == WB);
    assign  EX_or_WB   = state_EX || state_WB;

    /* define Instruction fields */
    assign  opcode = IR[31:26];
    assign      rs = IR[25:21];
    assign      rt = IR[20:16];
    assign      rd = IR[15:11];
    assign   shamt = IR[10: 6];
    assign    func = IR[ 5: 0];
    assign     imm = IR[15: 0];
    assign     tar = IR[25: 0];

    /* extend the immediate */
    assign imm_ZE = {        16'b0, imm};
    assign imm_SE = {{16{imm[15]}}, imm};


    /*
    ** define different types of instructions
    */

    assign  type_NOP = !(|IR);

    assign  type_R        = !(|opcode);
    assign  type_R_cal    = type_R && func[5];
    assign  type_R_shift  = type_R && !func[5] && !func[3];
    assign  type_R_j      = type_jr_mov && !func[1];
    assign  type_R_mov    = type_jr_mov && func[1];

    assign  type_J = !opcode[5] && !opcode[3] && !opcode[2] && opcode[1];

    assign  type_I        = (opcode[5] || opcode[3]) || type_I_branch;
    assign  type_I_cal    = !opcode[5] && opcode[3];
    assign  type_I_branch = !opcode[5] && !opcode[3] && opcode[2];
    assign  type_I_load   = opcode[5] && !opcode[3];
    assign  type_I_store  = opcode[5] && opcode[3];

    assign  type_RI_branch = !opcode[5] && !opcode[3] && (opcode[2:0] == 3'b001);

    assign  type_branch = type_I_branch || type_RI_branch;
    assign  type_i_b    = (opcode[5] != opcode[3]);
    assign  type_jr_mov = type_R && !func[5] && func[3];
    assign  type_jal    = type_R_j && func[0] || type_J && opcode[0];

    /* define whether to branch */
    assign branch_OK = opcode[2] && (   !opcode[1] && (opcode[0] != Zero) // beq, bne
                                     || opcode[1] && (opcode[0] != (alu_result[31] || Zero))) // blez, bgtz
                    || !opcode[2] && (alu_result[0] != rt[0]); // bltz, bgez(notice ALUop == SLT now)

    /* define specific instructions about memory reading and writing */
    assign  type_mem_b  = (opcode[1:0] == 2'b00);
    assign  type_mem_h  = (opcode[1:0] == 2'b01);
    assign  type_mem_w  = (opcode[2:0] == 3'b011);
    assign  type_mem_wl = (opcode[2:0] == 3'b010);
    assign  type_mem_wr = (opcode[2:0] == 3'b110);

    /* the low 2 bits of unligned address, from alu_result */
    assign  addr_00 = (alu_out[1:0] == 2'b00);
    assign  addr_01 = (alu_out[1:0] == 2'b01);
    assign  addr_10 = (alu_out[1:0] == 2'b10);
    assign  addr_11 = (alu_out[1:0] == 2'b11);

    /* }=========================================================================================================================== */



    /*
    ** {===========================================================================================================
    ** Finite State Machine(Three Stages)
    ** ============================================================================================================
    */


    /* first stage */
    always @(posedge clk) begin
        if (rst)
            current_state <= INIT;
        else
            current_state <= next_state;
    end


    /* second stage */
    assign next_state = {
                           {9{state_INIT}} & IF
                         | {9{state_IF  }} & (Inst_Req_Ready ? IW : IF)
                         | {9{state_IW  }} & (Inst_Valid ? ID : IW)
                         | {9{state_ID  }} & (type_NOP ? IF : EX)
                         | {9{state_EX  }} & {
                                                {9{type_I_load}} & LD
                                              | {9{type_I_store}} & ST
                                              | {9{type_R || type_I_cal || (type_J && opcode[0])}} & WB
                                              | {9{type_branch || (type_J && !opcode[0])}} & IF
                                           }
                         | {9{state_ST  }} & (Mem_Req_Ready ? IF : ST)
                         | {9{state_LD  }} & (Mem_Req_Ready ? RDW : LD)
                         | {9{state_RDW }} & (Read_data_Valid ? WB : RDW)
                         | {9{state_WB  }} & IF
    };


    /* third stage */
    assign Inst_Ready      = state_INIT || state_IW;
    assign Inst_Req_Valid  = state_IF;
    assign MemWrite        = state_ST;
    assign MemRead         = state_LD;
    assign Read_data_Ready = state_INIT || state_RDW;

    /* }=========================================================================================================== */



    /*
    ** {=====================================
    ** Instruction Register
    ** ======================================
    */

    always @(posedge clk) begin
        if (rst)
            IR <= 32'b0;
        else if (state_IW && Inst_Valid)
            IR <= Instruction;
    end


    /* {===================================== */



    /*
    ** {====================================================================================================================
    ** PC
    ** =====================================================================================================================
    */

    always @(posedge clk) begin
        if (rst)
            PC <= 32'b0;
        else
            PC <= {32{state_IF && Inst_Req_Ready}} & alu_result /* without Inst_Req_Ready, PC will keep adding */
                | {32{state_EX && type_branch && branch_OK}} & alu_out /* alu_out saves the branch address */
                | {32{state_EX && type_J}} & {PC[31:28], tar, 2'b0}
                | {32{state_EX && type_R_j}} & RF_rdata1
                | {32{!(   state_IF && Inst_Req_Ready
                        || state_EX && (type_branch && branch_OK || type_J || type_R_j))}
                  } & PC;
    end

    /* }==================================================================================================================== */



    /*
    ** {===================================================================================================
    ** Reg_File Ports
    ** ====================================================================================================
    */

    assign RF_raddr1 = rs;
    assign RF_raddr2 = rt;


    assign    RF_wen = state_WB && {   type_R_cal || type_R_shift || type_R_mov && (func[0] != Zero)
                                    || type_I_cal || type_I_load || type_jal};

    assign  RF_waddr = {5{type_R}} & rd
                     | {5{type_i_b}} & rt
                     | {5{type_J}}; /* 11111 */

    assign  RF_wdata = {32{type_R_shift}} & shifter_result
                     | {32{type_R_mov}} & RF_rdata1
                     | {32{type_I_cal && (&opcode[2:0])}} & {imm, 16'b0} // lui
                     | {32{type_I_load}} & R_data_mod
                     | {32{   type_R_cal
                           || type_I_cal && !(&opcode[2:0]) // addiu~sltiu
                           || type_J || type_R_j
                        }}  & alu_out;

    /* }=================================================================================================== */



    /*
    ** {=========================================================================================================================================
    ** ALU Ports
    ** ==========================================================================================================================================
    */

    /*
    ** alu_result and Zero from EX may be used in WB, but no registers can save them,
    ** so the ports must keep still from EX to WB
    */

    assign    alu_A = {32{state_IF || state_ID || EX_or_WB && type_jal}} & PC
                      /* !type_R_mov: if(mov), A = 0 */
                    | {32{!(state_IF || state_ID || EX_or_WB && type_jal) && !type_R_mov}} & RF_rdata1;

    assign    alu_B = {
                          {32{state_IF || EX_or_WB && type_jal}} & 32'h4
                        | {32{state_ID}} & {imm_SE[29:0], 2'b0}
                        | {32{EX_or_WB && (   type_R_cal
                                                         || type_branch && opcode[2] && !opcode[1] // beq, bne(when blez or bgez, B = 0)
                                                         || type_R_mov)
                            }}  & RF_rdata2
                        | {32{EX_or_WB && (   type_I_load
                                                         || type_I_store
                                                         || type_I_cal && !opcode[2]) // addiu, slti, sltiu
                            }}  & imm_SE
                        | {32{EX_or_WB && type_I_cal && opcode[2]}} // andi, ori, xori(lui included but not used)
                                & imm_ZE
    };


    assign    ALUop = {
                          {3{   state_IF
                             || state_ID
                             || state_EX && (type_I_load || type_I_store || type_jal)
                             || state_WB && type_jal
                          }}    & ADD
                        | {3{EX_or_WB && type_RI_branch}}
                                & SLT
                        | {3{EX_or_WB && (type_R_mov || type_I_branch)}}
                                & SUB /* when mov, test "rs - 0 ? 0" */
                        | {3{EX_or_WB && type_R_cal}}
                                & (
                                     {3{func[3]}} & {!func[0], 2'b11} // slt, sltu
                                   | {3{!func[3] && !func[2]}} & {func[1], 2'b10} // addu, subu
                                   | {3{!func[3] && func[2]}} & {func[1], 1'b0, func[0]} // and~xor
                                )
                        | {3{EX_or_WB && type_I_cal}}
                                & (
                                      {3{!opcode[2] && opcode[1]}} & {!opcode[0], 2'b11} // slti, sltiu
                                    | {3{!opcode[2] && !opcode[1]}} & ADD // addiu
                                    | {3{opcode[2]}} & {opcode[1], 1'b0, opcode[0]} // andi~xori,(lui included but not used)
                                )
    };


    always @(posedge clk) begin
        if (rst)
            alu_out <= 32'b0;
        else if (!(state_IW || state_LD || state_RDW || state_ST))
        /* when in waiting stage, keep still */
            alu_out <= alu_result;
    end

    /* }========================================================================================================================================= */



    /*
    ** {======================================================================
    ** Shifter Ports
    ** =======================================================================
    */

    assign  shifter_A = RF_rdata2;

    assign  shifter_B =   {5{type_R_shift && !func[2]}} // sll, sra, srl
                                & shamt
                        | {5{type_R_shift && func[2]}} // sllv, srav, srlv
                                & RF_rdata1[4:0];

    assign    Shiftop = func[1:0];

    /* }====================================================================== */



    /*
    ** {============================================================================================================
    ** Memory Operations
    ** =============================================================================================================
    */

    always @(posedge clk) begin
        if (rst)
            MDR <= 32'b0;
        else if (state_RDW && Read_data_Valid)
            MDR <= Read_data;
    end


    assign      Address = {alu_out[31:2], 2'b0};


    assign   Write_data = /* sb, swr */ {32{type_mem_b || type_mem_wr}} & {4{RF_rdata2[ 7: 0]}}
                        | /* sh      */ {32{type_mem_h}} & {2{RF_rdata2[15: 0]}}
                        | /* sw      */ {32{type_mem_w}} & RF_rdata2
                        | /* swl     */ {32{type_mem_wl}} & (
                                                  {32{addr_00}} & {24'b0, RF_rdata2[31:24]}
                                                | {32{addr_01}} & {16'b0, RF_rdata2[31:16]}
                                                | {32{addr_10}} & { 8'b0, RF_rdata2[31: 8]}
                                                | {32{addr_11}} & {       RF_rdata2[31: 0]}
                                        );

    assign   Write_strb = /* sb  */ {4{type_mem_b}} & (
                                              {4{addr_00}} & mask_byte1
                                            | {4{addr_01}} & mask_byte2
                                            | {4{addr_10}} & mask_byte3
                                            | {4{addr_11}} & mask_byte4
                                    )
                        | /* sh  */ {4{type_mem_h}} & (
                                              {4{addr_00}} & mask_low2
                                            | {4{addr_10}} & mask_high2
                                    )
                        | /* sw  */ {4{type_mem_w}} & mask_full
                        | /* swl */ {4{type_mem_wl}} & (
                                              {4{addr_00}} & mask_byte1
                                            | {4{addr_01}} & mask_low2
                                            | {4{addr_10}} & mask_low3
                                            | {4{addr_11}} & mask_full
                                    )
                        | /* swr */ {4{type_mem_wr}} & (
                                              {4{addr_00}} & mask_full
                                            | {4{addr_01}} & mask_high3
                                            | {4{addr_10}} & mask_high2
                                            | {4{addr_11}} & mask_byte4
                                    );


    assign   R_data_mod = /* lb, lbu */ {32{type_mem_b}} & (
                                                  {32{addr_00}} & {{24{MDR[ 7] && !opcode[2]}}, {MDR[ 7: 0]}}
                                                | {32{addr_01}} & {{24{MDR[15] && !opcode[2]}}, {MDR[15: 8]}}
                                                | {32{addr_10}} & {{24{MDR[23] && !opcode[2]}}, {MDR[23:16]}}
                                                | {32{addr_11}} & {{24{MDR[31] && !opcode[2]}}, {MDR[31:24]}}
                                        )
                        | /* lh, lhu */ {32{type_mem_h}} & (
                                                  {32{addr_00}} & {{16{MDR[15] && !opcode[2]}}, {MDR[15: 0]}}
                                                | {32{addr_10}} & {{16{MDR[31] && !opcode[2]}}, {MDR[31:16]}}
                                        )
                        | /* lw      */ {32{type_mem_w}} & $signed(MDR)
                        | /* lwl     */ {32{type_mem_wl}} & (
                                                  {32{addr_00}} & {MDR[ 7: 0], RF_rdata2[23: 0]}
                                                | {32{addr_01}} & {MDR[15: 0], RF_rdata2[15: 0]}
                                                | {32{addr_10}} & {MDR[23: 0], RF_rdata2[ 7: 0]}
                                                | {32{addr_11}} & {            RF_rdata2[31: 0]}
                                        )
                        | /* lwr     */ {32{type_mem_wr}} & (
                                                  {32{addr_00}} & {                  MDR[31: 0]}
                                                | {32{addr_01}} & {RF_rdata2[31:24], MDR[31: 8]}
                                                | {32{addr_10}} & {RF_rdata2[31:16], MDR[31:16]}
                                                | {32{addr_11}} & {RF_rdata2[31: 8], MDR[31:24]}
                                        );

    /* }============================================================================================================ */





    /*
    ** {======================================================
    ** Performance Counters
    ** =======================================================
    */


    assign cpu_perf_cnt_0  = cycle_cnt;
    assign cpu_perf_cnt_1  = ins_cnt;
    assign cpu_perf_cnt_2  = nop_cnt;
    assign cpu_perf_cnt_3  = IW_cnt;
    assign cpu_perf_cnt_4  = ST_cnt;
    assign cpu_perf_cnt_5  = LD_RDW_cnt;
    assign cpu_perf_cnt_6  = RI_cnt;
    assign cpu_perf_cnt_7  = I_b_cnt;
    assign cpu_perf_cnt_8  = branch_cnt;
    assign cpu_perf_cnt_9  = branchOK_cnt;
    assign cpu_perf_cnt_10 = jump_cnt;
    assign cpu_perf_cnt_11 = MemR_cnt;
    assign cpu_perf_cnt_12 = MemW_cnt;
    assign cpu_perf_cnt_13 = Memop_cnt;
    assign cpu_perf_cnt_14 = movOK_cnt;
    assign cpu_perf_cnt_15 = RFW_cnt;

    always @(posedge clk) begin
        if (rst)
            cycle_cnt <= 32'b0;
        else
            cycle_cnt <= cycle_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            ins_cnt <= 32'b0;
        else if (state_IF && Inst_Req_Ready)
            ins_cnt <= ins_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            nop_cnt <= 32'b0;
        else if (state_ID && type_NOP)
            /* ID last for 1 cycle */
            nop_cnt <= nop_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            IW_cnt <= 32'b0;
        else if (state_IW)
            IW_cnt <= IW_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            ST_cnt <= 32'b0;
        else if (state_ST)
            ST_cnt <= ST_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            LD_RDW_cnt <= 32'b0;
        else if (state_LD || state_RDW)
            LD_RDW_cnt <= LD_RDW_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            RI_cnt <= 32'b0;
        else if (state_ID && type_RI_branch)
            RI_cnt <= RI_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            I_b_cnt <= 32'b0;
        else if (state_ID && type_I_branch)
            I_b_cnt <= I_b_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            branch_cnt <= 32'b0;
        else if (state_ID && type_branch)
            branch_cnt <= branch_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            branchOK_cnt <= 32'b0;
        else if (state_EX && type_branch && branch_OK)
        /* branch_OK is valid only in EX */
            branchOK_cnt <= branchOK_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            jump_cnt <= 32'b0;
        else if (state_ID && (type_J || type_R_j))
            jump_cnt <= jump_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            MemR_cnt <= 32'b0;
        else if (state_ID && type_I_load)
            MemR_cnt <= MemR_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            MemW_cnt <= 32'b0;
        else if (state_ID && type_I_store)
            MemW_cnt <= MemW_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            Memop_cnt <= 32'b0;
        else if (state_ID && (type_I_load || type_I_store))
            Memop_cnt <= Memop_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            movOK_cnt <= 32'b0;
        else if (state_WB && type_R_mov && (func[0] != Zero))
            movOK_cnt <= movOK_cnt + 32'b1;
    end

    always @(posedge clk) begin
        if (rst)
            RFW_cnt <= 32'b0;
        else if (state_WB && RF_wen)
            RFW_cnt <= RFW_cnt + 32'b1;
    end

    /* }====================================================== */

endmodule