import Constants, Types;

function DecodedInst decode(bits(32) ir) =

  let opcode = ir[31:26]
  and funct  = ir[ 5: 0]
  in

  let rd1 =
    opcode == 6'b0 ? /* R-type instruction */
      funct == F_SLLV  ||
      funct == F_SRLV  ||
      funct == F_SRAV  ||
      funct == F_JR    ||
      funct == F_JALR  ||
      funct == F_MTHI  ||
      funct == F_MTLO  ||
      funct == F_MULT  ||
      funct == F_MULTU ||
      funct == F_DIV   ||
      funct == F_DIVU  ||
      funct == F_ADD   ||
      funct == F_ADDU  ||
      funct == F_SUB   ||
      funct == F_SUBU  ||
      funct == F_AND   ||
      funct == F_OR    ||
      funct == F_XOR   ||
      funct == F_NOR   ||
      funct == F_SLT   ||
      funct == F_SLTU :
    opcode == OP_BEQ   ||
    opcode == OP_BNE   ||
    opcode == OP_BLEZ  ||
    opcode == OP_BGTZ  ||
    opcode == OP_ADDI  ||
    opcode == OP_ADDIU ||
    opcode == OP_SLTI  ||
    opcode == OP_SLTIU ||
    opcode == OP_ANDI  ||
    opcode == OP_ORI   ||
    opcode == OP_XORI  ||
    opcode == OP_LB    ||
    opcode == OP_LH    ||
    opcode == OP_LW    ||
    opcode == OP_LBU   ||
    opcode == OP_LHU   ||
    opcode == OP_SB    ||
    opcode == OP_SH    ||
    opcode == OP_SW

  and rd2 =
    opcode == 6'b0 ? /* R-type instruction */
      funct == F_SLL ||
      funct == F_SRL ||
      funct == F_SRA ||
      funct == F_SLLV ||
      funct == F_SRLV ||
      funct == F_SRAV ||
      funct == F_MULT ||
      funct == F_MULTU ||
      funct == F_DIV ||
      funct == F_DIVU ||
      funct == F_ADD ||
      funct == F_ADDU ||
      funct == F_SUB ||
      funct == F_SUBU ||
      funct == F_AND ||
      funct == F_OR ||
      funct == F_XOR ||
      funct == F_NOR ||
      funct == F_SLT ||
      funct == F_SLTU :
    opcode == OP_BEQ ||
    opcode == OP_BNE ||
    opcode == OP_SB ||
    opcode == OP_SH ||
    opcode == OP_SW

  and wr =
    opcode == 6'b0 ?
      funct == F_SLL ||
      funct == F_SRL ||
      funct == F_SRA ||
      funct == F_SLLV ||
      funct == F_SRLV ||
      funct == F_SRAV ||
      funct == F_JALR ||
      funct == F_MFHI ||
      funct == F_MFLO ||
      funct == F_ADD ||
      funct == F_ADDU ||
      funct == F_SUB ||
      funct == F_SUBU ||
      funct == F_AND ||
      funct == F_OR ||
      funct == F_XOR ||
      funct == F_NOR ||
      funct == F_SLT ||
      funct == F_SLTU :
    opcode == OP_JAL ||
    opcode == OP_ADDI ||
    opcode == OP_ADDIU ||
    opcode == OP_SLTI ||
    opcode == OP_SLTIU ||
    opcode == OP_ANDI ||
    opcode == OP_ORI ||
    opcode == OP_XORI ||
    opcode == OP_LUI ||
    opcode == OP_LB ||
    opcode == OP_LH ||
    opcode == OP_LW ||
    opcode == OP_LBU ||
    opcode == OP_LHU
  in

  let rf_ra1 = rd1 ? ir[25:21] : 5'b0
  and rf_ra2 = rd2 ? ir[20:16] : 5'b0
  and rf_wa = wr ? (opcode == 6'b0 ? ir[15:11] : opcode == 6'd3/*JAL*/ ? 5'd31 : ir[20:16]) : 5'b0
  and shifter_op = funct[1:0]
  and alu_op =
    opcode == 6'b0 ?
      case (funct)
        6'd32, 6'd33: ALU_ADD;
	6'd34, 6'd35: ALU_SUB;
	6'd36: ALU_AND;
	6'd37: ALU_OR;
	6'd38: ALU_XOR;
	6'd39: ALU_NOR;
        6'd42: ALU_SLT;
	6'd43: ALU_ULT;
      end :
    opcode == OP_ADDI  ? ALU_ADD :
    opcode == OP_ADDIU ? ALU_ADD :
    opcode == OP_SLTI  ? ALU_SLT :
    opcode == OP_SLTIU ? ALU_ULT :
    opcode == OP_ANDI  ? ALU_AND :
    opcode == OP_ORI   ? ALU_OR  :
    opcode == OP_XORI  ? ALU_XOR :
    ALU_ADD
  and alu_b_imm = opcode != 6'b0
  and shamt_imm = !funct[2]
  and next_pc_sel =
    opcode == 6'b0 ? (funct[5:1] == 5'b00100 ? NextPC_RS : NextPC_NoJump) :
    opcode[5:1] == 5'b00001 ? NextPC_J :
    opcode[5:2] == 4'b0001 ? NextPC_B :
    NextPC_NoJump
  and cond_sel = opcode[1:0]
  and imm_ext_method =
    opcode == OP_ANDI || opcode == OP_ORI || opcode == OP_XORI ? ZeroExt :
    opcode == OP_LUI ? LUI_Ext :
    SignExt
  and dm_rd =
    case (opcode)
      OP_LB, OP_LBU, OP_LH, OP_LHU, OP_LW: true;
      default: false;
    end
  and dm_wr =
    opcode == OP_SB ||
    opcode == OP_SH ||
    opcode == OP_SW
  and dm_req_size =
    case (opcode)
      OP_LB, OP_LBU, OP_SB: Byte;
      OP_LH, OP_LHU, OP_SH: Half;
      OP_LW, OP_SW: Word;
    end
  and rf_in_sel =
    case (opcode)
      6'b0:
        funct[5:3] == 3'b0 ? ShifterOut :
        funct == F_JALR ? PC_plus8 :
        ALU_Out;
      OP_JAL: PC_plus8;
      OP_ADDI, OP_ADDIU, OP_SLTI, OP_SLTIU, OP_ANDI, OP_ORI, OP_XORI, OP_LUI:
        ALU_Out;
      OP_LB, OP_LBU, OP_LH, OP_LHU, OP_LW: DM_Out;
    end
  and mem_data_sign_ext = opcode == OP_LB || opcode == OP_LH
  in

  DecodedInst{
    rf_ra1, rf_ra2, rf_wa,
    alu_b_imm, shamt_imm,
    next_pc_sel, cond_sel, imm_ext_method,
    dm_en: dm_rd || dm_wr, dm_wr, dm_req_size,
    rf_in_sel, mem_data_sign_ext,
    shifter_op, alu_op
  };
