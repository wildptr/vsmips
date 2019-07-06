import Types, Decode, ALU, RegFile, DataHazard, DMem;

typedef bits(30) PC;

struct ExecuteStage {
  bits(32) r1;
  bits(32) r2;
  bits(32) imm32;
  RegIndex rf_wa; /* 0 if instruction does not write register */
  RegFileInput rf_in_sel;
  ShifterOp shifter_op;
  ALU_Op alu_op;
  bool alu_b_imm;
  bool shamt_imm;
  bits(5) shamt; /* instruction[10:6] */
  bool dm_en;
  bool dm_wr;
  MemReqSize dm_req_size;
  bool mem_data_sign_ext;
  PC pc;
};

struct MemoryStage {
  bool dm_en;
  bool dm_wr;
  MemReqSize dm_req_size;
  bits(32) dm_in;
  bits(32) alu_out;
  bits(32) shifter_out;
  RegIndex rf_wa;
  RegFileInput rf_in_sel;
  bool mem_data_sign_ext;
  PC pc;
};

struct WritebackStage {
  bits(32) alu_out;
  bits(32) shifter_out;
  RegIndex rf_wa;
  RegFileInput rf_in_sel;
  MemReqSize dm_req_size; /* for data extension */
  bool mem_data_sign_ext;
  PC pc;
};

function bits(32) rf_in(WritebackStage wb, bits(32) dm_out) =
  case (wb.rf_in_sel)
    ALU_Out: wb.alu_out;
    ShifterOut: wb.shifter_out;
    DM_Out:
      case (wb.dm_req_size)
        Byte:
          wb.mem_data_sign_ext ?
            sign_extend(32, dm_out[7:0]) :
            zero_extend(32, dm_out[7:0]);
        Half:
          wb.mem_data_sign_ext ?
            sign_extend(32, dm_out[15:0]) :
            zero_extend(32, dm_out[15:0]);
        Word: dm_out;
      end;
    PC_plus8: {wb.pc+30'd1, 2'b0};
  end;

function bits(30) next_pc(bits(30) pc, bool stop, bits(32) inst, DecodedInst dinst, bits(32) r1, bits(32) r2) =
  case (dinst.next_pc_sel)
    NextPC_NoJump: stop ? pc : pc+30'b1;
    NextPC_RS: r1[31:2];
    NextPC_J: {pc[29:26],inst[25:0]};
    NextPC_B:
      case (dinst.cond_sel)
        CondEQ: r1 == r2;
        CondNE: r1 != r2;
        CondLEZ: r1 signed <= 32'b0;
        CondGTZ: r1 signed > 32'b0;
      end ? pc + sign_extend(30, inst[15:0]) : pc;
  end;

module mips(
  input bool reset,
  input bool stop,
  input bits(32) im_din,
  // input bits(32) dm_din,
  output bool im_en,
  output PC im_addr/*,
  output bool dm_en,
  output bool dm_wr,
  output bits(32) dm_addr,
  output MemReqSize dm_req_size,
  output bits(32) dm_dout*/)

  /* state elements */
  reg PC pc;
  instance regfile rf;
  instance dmem dm;
  reg bool de_valid;
  reg bits(32) inst;
  reg ExecuteStage ex;
  reg MemoryStage mem;
  reg WritebackStage wb;

  /* value declarations */

  val DecodedInst dinst;
  val bits(32) r1, r2;
  val bits(16) imm16;
  val bits(32) imm32;
  val bits(32) alu_out, shifter_out;
  val bits(32) dm_out;

  val bool stall;

  /**/

  pc <= reset ? 30'b0 : next_pc(pc, stop, inst, dinst, r1, r2) when reset || !stall;

  de_valid <= reset ? false : dinst.next_pc_sel == NextPC_NoJump && !stop
    when reset || !stall;

  ex <=
    reset ?
      ExecuteStage{
        r1: undef(bits(32)),
        r2: undef(bits(32)),
        imm32: undef(bits(32)),
        rf_wa: 5'b0,
        rf_in_sel: undef(RegFileInput),
        shifter_op: undef(ShifterOp),
        alu_op: undef(ALU_Op),
        alu_b_imm: undef(bool),
        shamt_imm: undef(bool),
        shamt: undef(bits(5)),
        dm_en: false,
        dm_wr: undef(bool),
        dm_req_size: undef(MemReqSize),
        mem_data_sign_ext: undef(bool),
        pc: undef(PC)} :
      ExecuteStage{
        r1, r2, imm32,
        rf_wa: stall ? 5'b0 : dinst.rf_wa,
        rf_in_sel: dinst.rf_in_sel,
        shifter_op: dinst.shifter_op,
        alu_op: dinst.alu_op,
        alu_b_imm: dinst.alu_b_imm,
        shamt_imm: dinst.shamt_imm,
        shamt: inst[10:6],
        dm_en: stall ? false : dinst.dm_en,
        dm_wr: dinst.dm_wr,
        dm_req_size: dinst.dm_req_size,
        mem_data_sign_ext: dinst.mem_data_sign_ext,
        pc};

  mem <=
    reset ?
      MemoryStage{
        dm_en: false,
        dm_wr: undef(bool),
        dm_req_size: undef(MemReqSize),
        dm_in: undef(bits(32)),
        alu_out: undef(bits(32)),
        shifter_out: undef(bits(32)),
        rf_wa: 5'b0,
        rf_in_sel: undef(RegFileInput),
        mem_data_sign_ext: undef(bool),
        pc: undef(PC)} :
      MemoryStage{
        dm_en: ex.dm_en,
        dm_wr: ex.dm_wr,
        dm_req_size: ex.dm_req_size,
        dm_in: ex.r2,
        alu_out, shifter_out,
        rf_wa: ex.rf_wa,
        rf_in_sel: ex.rf_in_sel,
        mem_data_sign_ext: ex.mem_data_sign_ext,
        pc: ex.pc};

  wb <=
    reset ?
      WritebackStage{
        alu_out: undef(bits(32)),
        shifter_out: undef(bits(32)),
        rf_wa: 5'b0,
        rf_in_sel: undef(RegFileInput),
        dm_req_size: undef(MemReqSize),
        mem_data_sign_ext: undef(bool),
        pc: undef(PC)} :
      WritebackStage{
        alu_out: mem.alu_out,
        shifter_out: mem.shifter_out,
        rf_wa: mem.rf_wa,
        rf_in_sel: mem.rf_in_sel,
        dm_req_size: mem.dm_req_size,
        mem_data_sign_ext: mem.mem_data_sign_ext,
        pc: mem.pc};

  im_addr = pc;
  inst <= im_din when !stall;
  dinst = de_valid ? decode(inst) :
    DecodedInst{
      rf_ra1: 5'b0,
      rf_ra2: 5'b0,
      rf_wa: 5'b0,
      shifter_op: undef(ShifterOp),
      alu_op: undef(ALU_Op),
      alu_b_imm: undef(bool),
      shamt_imm: undef(bool),
      next_pc_sel: NextPC_NoJump,
      cond_sel: undef(Cond),
      imm_ext_method: undef(ImmExtMethod),
      dm_en: false,
      dm_wr: undef(bool),
      dm_req_size: undef(MemReqSize),
      rf_in_sel: undef(RegFileInput),
      mem_data_sign_ext: undef(bool)};

  rf(
    ra1: dinst.rf_ra1,
    ra2: dinst.rf_ra2,
    out1: r1,
    out2: r2,
    wa: wb.rf_wa,
    in1: rf_in(wb, dm_out));

  imm16 = inst[15:0];
  imm32 =
    case (dinst.imm_ext_method)
      ZeroExt: zero_extend(32, imm16);
      SignExt: sign_extend(32, imm16);
      LUI_Ext: {imm16, 16'b0};
    end;

  alu_out = alu(ex.r1, ex.alu_b_imm ? ex.imm32 : ex.r2, ex.alu_op);
  shifter_out = shifter(ex.r2, ex.shamt_imm ? ex.shamt : ex.r1[4:0], ex.shifter_op);

  dm(
    en: mem.dm_en,
    wr: mem.dm_wr,
    addr: mem.alu_out,
    size1: mem.dm_req_size,
    in1: mem.dm_in,
    out: dm_out);

  im_en = reset || !stall;

  stall = data_hazard(ex.rf_wa, mem.rf_wa, dinst.rf_ra1, dinst.rf_ra2);

end; /* module mips */
