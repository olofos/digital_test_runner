module \74779_tb ();
  reg  CP = 0;
  reg  S0 = 0;
  reg  S1 = 0;
  reg  \~OE = 1;
  wire \I/O0 ;
  wire \I/O1 ;
  wire \I/O2 ;
  wire \I/O3 ;
  wire \I/O4 ;
  wire \I/O5 ;
  wire \I/O6 ;
  wire \I/O7 ;
  reg  \~CET = 0;
  reg  VCC = 0;
  reg  GND = 0;
  wire \~TC ;

  reg  \I/O0_reg = 'Z;
  reg  \I/O1_reg = 'Z;
  reg  \I/O2_reg = 'Z;
  reg  \I/O3_reg = 'Z;
  reg  \I/O4_reg = 'Z;
  reg  \I/O5_reg = 'Z;
  reg  \I/O6_reg = 'Z;
  reg  \I/O7_reg = 'Z;

  assign \I/O0 = \I/O0_reg ;
  assign \I/O1 = \I/O1_reg ;
  assign \I/O2 = \I/O2_reg ;
  assign \I/O3 = \I/O3_reg ;
  assign \I/O4 = \I/O4_reg ;
  assign \I/O5 = \I/O5_reg ;
  assign \I/O6 = \I/O6_reg ;
  assign \I/O7 = \I/O7_reg ;

  reg [12:0] in;

  integer exit, res;

  \74779 dut (
      CP,
      S0,
      S1,
      \~OE ,
      \I/O0 ,
      \I/O1 ,
      \I/O2 ,
      \I/O3 ,
      \I/O4 ,
      \I/O5 ,
      \I/O6 ,
      \I/O7 ,
      \~CET ,
      VCC,
      GND,
      \~TC
  );
  initial begin
    $dumpfile("/tmp/out");
    $dumpvars(0, dut);
    exit = 0;
    while (!exit) begin
      res = $fscanf('h8000_0000, "%b", in);
      if (res == 1)
        {CP, S0, S1, \~OE , \I/O0_reg , \I/O1_reg , \I/O2_reg , \I/O3_reg , \I/O4_reg , \I/O5_reg , \I/O6_reg , \I/O7_reg , \~CET , VCC, GND} = in;
      else exit = 1;
      #10;
      $fwrite('h8000_0001, "> %b\n", {\I/O0 , \I/O1 , \I/O2 , \I/O3 , \I/O4 , \I/O5 , \I/O6 ,
                                      \I/O7 , \~TC });
      $fflush('h8000_0001);
    end
  end
endmodule
