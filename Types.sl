typedef bits(5) RegIndex;

enum NextPC {
  NextPC_NoJump,
  NextPC_RS,
  NextPC_J,
  NextPC_B
};

enum RegFileInput {
  ALU_Out,
  ShifterOut,
  DM_Out,
  PC_plus8
};

typedef bits(2) Cond;
typedef bits(2) ShifterOp;
typedef bits(4) ALU_Op;

enum ImmExtMethod {
  ZeroExt,
  SignExt,
  LUI_Ext
};

enum MemReqSize { Byte, Half, Word };

struct DecodedInst {
  RegIndex rf_ra1; /* 0 if instruction does not read register */
  RegIndex rf_ra2; /* same as above */
  RegIndex rf_wa; /* 0 if instruction does not write register */
  ShifterOp shifter_op;
  ALU_Op alu_op;
  bool alu_b_imm;
  bool shamt_imm;
  NextPC next_pc_sel;
  Cond cond_sel;
  ImmExtMethod imm_ext_method;
  bool dm_en;
  bool dm_wr;
  MemReqSize dm_req_size;
  RegFileInput rf_in_sel;
  bool mem_data_sign_ext;
};
