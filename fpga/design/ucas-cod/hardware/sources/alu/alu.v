`timescale 10 ns / 1 ns
`define DATA_WIDTH 32

module alu (
    input  [`DATA_WIDTH - 1:0] A,
    input  [`DATA_WIDTH - 1:0] B,
    input  [2:0] ALUop,
    output Overflow,
    output CarryOut,
    output Zero,
    output [`DATA_WIDTH - 1:0] Result
);


wire [`DATA_WIDTH:0] add_result = {1'b0, A} + {1'b0, B};
wire [`DATA_WIDTH:0] sub_result = {1'b0, A} + {1'b1, ~B} + 1'b1;


wire add_overflow = (A[`DATA_WIDTH-1] == B[`DATA_WIDTH-1]) && 
                   (add_result[`DATA_WIDTH-1] != A[`DATA_WIDTH-1]);
                   
wire sub_overflow = (A[`DATA_WIDTH-1] != B[`DATA_WIDTH-1]) && 
                   (sub_result[`DATA_WIDTH-1] != A[`DATA_WIDTH-1]);


wire slt_result;
assign slt_result = 
    (A[`DATA_WIDTH-1] & !B[`DATA_WIDTH-1]) ? 1'b1 :
    (!A[`DATA_WIDTH-1] & B[`DATA_WIDTH-1]) ? 1'b0 :
    (sub_overflow ^ sub_result[`DATA_WIDTH-1]);  

wire sub_carryout = sub_result[`DATA_WIDTH];

assign Result = 
    (ALUop == 3'b000) ? (A & B) :
    (ALUop == 3'b001) ? (A | B) :
    (ALUop == 3'b010) ? (A + B) :
    (ALUop == 3'b110) ? sub_result[`DATA_WIDTH-1:0] :
    (ALUop == 3'b111) ? {{(`DATA_WIDTH-1){1'b0}}, slt_result} :
    {`DATA_WIDTH{1'bx}};

assign Zero = (Result == 0);

assign CarryOut = 
    (ALUop == 3'b010) ? add_result[`DATA_WIDTH] :
    (ALUop == 3'b110 | ALUop == 3'b111) ? sub_carryout :
    1'b0;

assign Overflow = 
    (ALUop == 3'b010) ? (A[`DATA_WIDTH-1] == B[`DATA_WIDTH-1] && Result[`DATA_WIDTH-1] != A[`DATA_WIDTH-1]) :
    (ALUop == 3'b110) ? (A[`DATA_WIDTH-1] != B[`DATA_WIDTH-1] && Result[`DATA_WIDTH-1] != A[`DATA_WIDTH-1]) :
    (ALUop == 3'b111) ? (A[`DATA_WIDTH-1] ^ B[`DATA_WIDTH-1]) & (A[`DATA_WIDTH-1] ^ Result[`DATA_WIDTH-1]) :
    1'b0;

endmodule
