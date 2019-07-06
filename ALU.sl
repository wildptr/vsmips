import Constants, Types;

function bits(32) alu(bits(32) a, bits(32) b, ALU_Op op) =
  case (op)
    ALU_ADD: a + b;
    ALU_SUB: a - b;
    ALU_SLT: a signed < b ? 32'b1 : 32'b0;
    ALU_ULT: a        < b ? 32'b1 : 32'b0;
    ALU_AND: a & b;
    ALU_OR : a | b;
    ALU_XOR: a ^ b;
    ALU_NOR: ~(a|b);
  end;

function bits(32) shifter(bits(32) in1, bits(5) shamt, ShifterOp op) =
  case (op)
    SHL, 2'b01: in1 <<  shamt;
    LSHR:       in1 >>  shamt;
    ASHR:       in1 >>> shamt;
  end;
