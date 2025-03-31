`timescale 10 ns / 1 ns

`define DATA_WIDTH 32

module shifter (
    input  [`DATA_WIDTH - 1:0] A,
    input  [              4:0] B,
    input  [              1:0] Shiftop,
    output [`DATA_WIDTH - 1:0] Result
);
  // TODO: Please add your logic code here
  wire en_shift_L = ~Shiftop[1] & ~Shiftop[0];
  wire en_shift_RL = Shiftop[1] & Shiftop[0];
  wire en_shift_RA = Shiftop[1] & ~Shiftop[0];

  wire [`DATA_WIDTH - 1:0] shift_L = A << B & {`DATA_WIDTH{en_shift_L}};
  wire [`DATA_WIDTH - 1:0] shift_RL = A >> B & {`DATA_WIDTH{en_shift_RL}};
  wire [`DATA_WIDTH - 1:0] shift_RA = $signed(A) >>> B & {`DATA_WIDTH{en_shift_RA}};
  assign Result = shift_L | shift_RL | shift_RA;
endmodule
