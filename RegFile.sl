module regfile(
  input bits(5) ra1,
  input bits(5) ra2,
  input bits(5) wa,
  input bits(32) in1,
  output bits(32) out1,
  output bits(32) out2)

  reg bits(5)[bits(32)] r;

  out1 = ra1 == 5'b0 ? 32'b0 : wa == ra1 ? in1 : r[ra1];
  out2 = ra2 == 5'b0 ? 32'b0 : wa == ra2 ? in1 : r[ra2];

  r <= r[wa := in1] when wa != 5'b0;

end;
