module Counter (
    input CLK,
    input RESET,
    output reg [3:0] OUT
);

  always @(posedge CLK) begin
    if (RESET == 1 || OUT == 9) OUT <= 0;
    else OUT <= OUT + 1;
  end

  initial begin
    OUT <= 11;
  end

endmodule

module InteractiveTb ();
  reg CLK = 0;
  reg RESET = 0;
  wire [3:0] OUT;

  reg [1:0] in;

  integer res, exit, step;
  string sig;

  Counter dut (
      CLK,
      RESET,
      OUT
  );

  initial begin
    exit = 0;
    while (!exit) begin
      step = 0;
      while (!step) begin
        res = $fscanf('h8000_0000, "%s", sig);
        if (res == 1) begin
          if (sig == "STEP") step = 1;
          else begin
            res = $fscanf('h8000_0000, "%d", in);
            if (res == 1) begin
              if (sig == "CLK") CLK = in;
              else if (sig == "RESET") RESET = in;
            end else begin
              exit = 1;
              step = 1;
            end
          end
        end else begin
          exit = 1;
          step = 1;
        end
      end
      #1;
      $fwrite('h8000_0001, "OUT %d\n", OUT);
      $fwrite('h8000_0001, "\n");
      $fflush('h8000_0001);
    end
  end
endmodule
