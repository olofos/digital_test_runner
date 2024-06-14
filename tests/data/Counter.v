module Counter (
    input CLK,
    input RESET,
    output reg [3:0] OUT,
    output TC
);

  assign TC = OUT == 9;
  always @(posedge CLK) begin
    if (RESET == 1 || OUT == 9) OUT <= 0;
    else OUT <= OUT + 1;
  end

  initial begin
    OUT <= 11;
  end

endmodule
