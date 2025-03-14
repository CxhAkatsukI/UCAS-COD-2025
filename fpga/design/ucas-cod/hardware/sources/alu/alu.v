`timescale 10 ns / 1 ns

`define DATA_WIDTH 32

module alu (
    input  [`DATA_WIDTH - 1:0] A,
    input  [`DATA_WIDTH - 1:0] B,
    input  [              2:0] ALUop,
    output                     Overflow,
    output                     CarryOut,
    output                     Zero,
    output [`DATA_WIDTH - 1:0] Result
);
  // TODO: Please add your logic design here
  wire [`DATA_WIDTH - 1:0] temp_result;
  wire [`DATA_WIDTH - 1:0] temp;

  assign Result = ALUop == 3'b000 ? (A & B) : Result;
  assign Zero = ALUop == 3'b000 ? ((ALUop == 3'b000 ? (A & B) : Result) == {`DATA_WIDTH{0}}) : Zero;

  assign Result = ALUop == 3'b001 ? (A | B) : Result;
  assign Zero = ALUop == 3'b001 ? ((ALUop == 3'b001 ? (A | B) : Result) == {`DATA_WIDTH{0}}) : Zero;

  assign {CarryOut, Result} = ALUop == 3'b010 ? (A + B) : {CarryOut, Result};
  assign Overflow    = ALUop == 3'b010 ? (A[`DATA_WIDTH - 1] == B[`DATA_WIDTH - 1] && A[`DATA_WIDTH - 1] != Result[`DATA_WIDTH - 1]) : Overflow;
  assign Zero        = ALUop == 3'b010 ? ((ALUop == 3'b010 ? Result : {`DATA_WIDTH{1'bx}}) == {`DATA_WIDTH{0}}) : Zero;

  assign temp = ALUop == 3'b110 ? ~B : temp;
  assign {CarryOut, Result} = ALUop == 3'b110 ? (A + temp + 1'b1) : {CarryOut, Result};
  assign Overflow        = ALUop == 3'b110 ? (Result[`DATA_WIDTH-1] ^ A[`DATA_WIDTH-1] ^ B[`DATA_WIDTH-1]) : Overflow;
  assign Zero            = ALUop == 3'b110 ? ((ALUop == 3'b110 ? Result : {`DATA_WIDTH{1'bx}}) == {`DATA_WIDTH{0}}) : Zero;

  assign temp = ALUop == 3'b111 ? ~B : temp;
  assign {CarryOut, temp_result} = ALUop == 3'b111 ? (A + temp + 1'b1) : {CarryOut, temp_result};
  assign Overflow          = ALUop == 3'b111 ? (A[`DATA_WIDTH - 1] == B[`DATA_WIDTH - 1] && A[`DATA_WIDTH - 1] != temp_result[`DATA_WIDTH - 1]) : Overflow;
  assign Zero              = ALUop == 3'b111 ? ((ALUop == 3'b111 ? temp_result[`DATA_WIDTH-1:0] : {`DATA_WIDTH{1'bx}}) == {`DATA_WIDTH{0}}) : Zero;
  assign Result = ALUop == 3'b111 ? {{(`DATA_WIDTH - 1) {0}}, temp_result[`DATA_WIDTH-1]} : Result;


endmodule
