import Types;

module dmem(
  input bool en,
  input bool wr,
  input bits(32) addr,
  input MemReqSize size1,
  input bits(32) in1,
  output bits(32) out)

  reg bits(12)[bits(8)] m;
  reg bits(32) out_r;

  /* read */
  out_r <=
    case (size1)
      Byte: {24'b0, m[addr[11:0]]};
      Half: {16'b0, m[{addr[11:1],1'b1}],
                    m[{addr[11:1],1'b0}]};
      Word: {       m[{addr[11:2],2'h3}],
                    m[{addr[11:2],2'h2}],
                    m[{addr[11:2],2'h1}],
                    m[{addr[11:2],2'h0}]};
    end
    when en && !wr;
  out = out_r;

  /* write */
  m <=
    case (size1)
      Byte: m[addr[11:0] := in1[7:0]];
      Half: m[{addr[11:1],1'b0} := in1[ 7: 0]]
             [{addr[11:1],1'b1} := in1[15: 8]];
      Word: m[{addr[11:2],2'h0} := in1[ 7: 0]]
             [{addr[11:2],2'h1} := in1[15: 8]]
             [{addr[11:2],2'h2} := in1[23:16]]
             [{addr[11:2],2'h3} := in1[31:24]];
    end
    when en && wr;

end; /* module dmem */
