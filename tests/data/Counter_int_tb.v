
module InteractiveTb ();
  reg CLK = 0;
  reg RESET = 0;
  wire [3:0] OUT;
  wire TC;

  reg [1:0] in;

  integer exit, res;

  Counter dut (
      CLK,
      RESET,
      OUT,
      TC
  );

  initial begin
    exit = 0;
    while (!exit) begin
      res = $fscanf('h8000_0000, "%b", in);
      if (res == 1) {CLK, RESET} = in;
      else exit = 1;
      #1;
      $fwrite('h8000_0001, "%b\n", {OUT, TC});
      $fflush('h8000_0001);
    end
  end
endmodule
