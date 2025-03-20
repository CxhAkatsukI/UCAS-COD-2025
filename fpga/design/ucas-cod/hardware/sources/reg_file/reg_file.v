`timescale 10 ns / 1 ns

`define DATA_WIDTH 32
`define ADDR_WIDTH 5

module reg_file (
    input                      clk,
    input  [`ADDR_WIDTH - 1:0] waddr,
    input  [`ADDR_WIDTH - 1:0] raddr1,
    input  [`ADDR_WIDTH - 1:0] raddr2,
    input                      wen,
    input  [`DATA_WIDTH - 1:0] wdata,
    output [`DATA_WIDTH - 1:0] rdata1,
    output [`DATA_WIDTH - 1:0] rdata2
);

  // TODO: Please add your logic design here
  reg [`DATA_WIDTH - 1:0] data_array[`DATA_WIDTH - 1:0];
  always @(posedge clk) begin
    if (wen && waddr != 0) begin
      data_array[waddr] <= wdata;
    end
  end
  assign rdata1 = (raddr1 == {`ADDR_WIDTH{1'b0}} ? {`ADDR_WIDTH{1'b0}} : data_array[raddr1]);
  assign rdata2 = (raddr2 == {`ADDR_WIDTH{1'b0}} ? {`ADDR_WIDTH{1'b0}} : data_array[raddr2]);

endmodule
