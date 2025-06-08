`timescale 10 ns / 1 ns

`define TARRAY_ADDR_WIDTH 3

module custom_array #(
    // Define a parameter for the data width
    // Provide a default value for it
    parameter TARRAY_DATA_WIDTH = 24
) (
    input                               clk,
    input  [`TARRAY_ADDR_WIDTH - 1 : 0] waddr, // Address width can also be a parameter if needed
    input  [`TARRAY_ADDR_WIDTH - 1 : 0] raddr,
    input                               wen,
    input                               rst,
    input  [TARRAY_DATA_WIDTH - 1 : 0]  wdata, // Use the parameter here
    output [TARRAY_DATA_WIDTH - 1 : 0]  rdata  // Use the parameter here
);

    // The size of the array elements will now depend on the TARRAY_DATA_WIDTH parameter
    reg [TARRAY_DATA_WIDTH - 1 : 0] array [(1 << `TARRAY_ADDR_WIDTH) - 1 : 0];
    integer i;

    always @(posedge clk) begin
        if (rst) begin
          for (i = 0; i < (1 << `TARRAY_ADDR_WIDTH); i = i + 1)
            array[i] <= 1'b0;
        end else if (wen)
            array[waddr] <= wdata;
    end

    assign rdata = array[raddr];

endmodule
