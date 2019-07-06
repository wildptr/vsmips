theory MIPS_Model imports Word_Lib.Word_Lib begin
datatype NextPC = NextPC_NoJump | NextPC_RS | NextPC_J | NextPC_B
datatype RegFileInput = ALU_Out | ShifterOut | DM_Out | PC_plus8
datatype ImmExtMethod = ZeroExt | SignExt | LUI_Ext
datatype MemReqSize = Byte | Half | Word
record DecodedInst =
  DecodedInst_rf_ra1 :: \<open>5 word\<close>
  DecodedInst_rf_ra2 :: \<open>5 word\<close>
  DecodedInst_rf_wa :: \<open>5 word\<close>
  DecodedInst_shifter_op :: \<open>2 word\<close>
  DecodedInst_alu_op :: \<open>4 word\<close>
  DecodedInst_alu_b_imm :: \<open>bool\<close>
  DecodedInst_shamt_imm :: \<open>bool\<close>
  DecodedInst_next_pc_sel :: \<open>NextPC\<close>
  DecodedInst_cond_sel :: \<open>2 word\<close>
  DecodedInst_imm_ext_method :: \<open>ImmExtMethod\<close>
  DecodedInst_dm_en :: \<open>bool\<close>
  DecodedInst_dm_wr :: \<open>bool\<close>
  DecodedInst_dm_req_size :: \<open>MemReqSize\<close>
  DecodedInst_rf_in_sel :: \<open>RegFileInput\<close>
  DecodedInst_mem_data_sign_ext :: \<open>bool\<close>
definition eqnz :: \<open>5 word \<Rightarrow> 5 word \<Rightarrow> bool\<close> where
  \<open>eqnz a b \<equiv> ((a = b) \<and> (a \<noteq> (0 :: 5 word)))\<close>
definition data_hazard :: \<open>5 word \<Rightarrow> 5 word \<Rightarrow> 5 word \<Rightarrow> 5 word \<Rightarrow> bool\<close> where
  \<open>data_hazard wa_E wa_M ra1_D ra2_D \<equiv> ((((eqnz ra1_D wa_E) \<or> (eqnz ra2_D wa_E)) \<or> (eqnz ra1_D wa_M)) \<or> (eqnz ra2_D wa_M))\<close>
abbreviation (input) \<open>F_SLL \<equiv> (0 :: 6 word)\<close>
abbreviation (input) \<open>F_SRL \<equiv> (2 :: 6 word)\<close>
abbreviation (input) \<open>F_SRA \<equiv> (3 :: 6 word)\<close>
abbreviation (input) \<open>F_SLLV \<equiv> (4 :: 6 word)\<close>
abbreviation (input) \<open>F_SRLV \<equiv> (6 :: 6 word)\<close>
abbreviation (input) \<open>F_SRAV \<equiv> (7 :: 6 word)\<close>
abbreviation (input) \<open>F_JR \<equiv> (8 :: 6 word)\<close>
abbreviation (input) \<open>F_JALR \<equiv> (9 :: 6 word)\<close>
abbreviation (input) \<open>F_SYSCALL \<equiv> (12 :: 6 word)\<close>
abbreviation (input) \<open>F_MFHI \<equiv> (16 :: 6 word)\<close>
abbreviation (input) \<open>F_MTHI \<equiv> (17 :: 6 word)\<close>
abbreviation (input) \<open>F_MFLO \<equiv> (18 :: 6 word)\<close>
abbreviation (input) \<open>F_MTLO \<equiv> (19 :: 6 word)\<close>
abbreviation (input) \<open>F_MULT \<equiv> (24 :: 6 word)\<close>
abbreviation (input) \<open>F_MULTU \<equiv> (25 :: 6 word)\<close>
abbreviation (input) \<open>F_DIV \<equiv> (26 :: 6 word)\<close>
abbreviation (input) \<open>F_DIVU \<equiv> (27 :: 6 word)\<close>
abbreviation (input) \<open>F_ADD \<equiv> (32 :: 6 word)\<close>
abbreviation (input) \<open>F_ADDU \<equiv> (33 :: 6 word)\<close>
abbreviation (input) \<open>F_SUB \<equiv> (34 :: 6 word)\<close>
abbreviation (input) \<open>F_SUBU \<equiv> (35 :: 6 word)\<close>
abbreviation (input) \<open>F_AND \<equiv> (36 :: 6 word)\<close>
abbreviation (input) \<open>F_OR \<equiv> (37 :: 6 word)\<close>
abbreviation (input) \<open>F_XOR \<equiv> (38 :: 6 word)\<close>
abbreviation (input) \<open>F_NOR \<equiv> (39 :: 6 word)\<close>
abbreviation (input) \<open>F_SLT \<equiv> (42 :: 6 word)\<close>
abbreviation (input) \<open>F_SLTU \<equiv> (43 :: 6 word)\<close>
abbreviation (input) \<open>OP_J \<equiv> (2 :: 6 word)\<close>
abbreviation (input) \<open>OP_JAL \<equiv> (3 :: 6 word)\<close>
abbreviation (input) \<open>OP_BEQ \<equiv> (4 :: 6 word)\<close>
abbreviation (input) \<open>OP_BNE \<equiv> (5 :: 6 word)\<close>
abbreviation (input) \<open>OP_BLEZ \<equiv> (6 :: 6 word)\<close>
abbreviation (input) \<open>OP_BGTZ \<equiv> (7 :: 6 word)\<close>
abbreviation (input) \<open>OP_ADDI \<equiv> (8 :: 6 word)\<close>
abbreviation (input) \<open>OP_ADDIU \<equiv> (9 :: 6 word)\<close>
abbreviation (input) \<open>OP_SLTI \<equiv> (10 :: 6 word)\<close>
abbreviation (input) \<open>OP_SLTIU \<equiv> (11 :: 6 word)\<close>
abbreviation (input) \<open>OP_ANDI \<equiv> (12 :: 6 word)\<close>
abbreviation (input) \<open>OP_ORI \<equiv> (13 :: 6 word)\<close>
abbreviation (input) \<open>OP_XORI \<equiv> (14 :: 6 word)\<close>
abbreviation (input) \<open>OP_LUI \<equiv> (15 :: 6 word)\<close>
abbreviation (input) \<open>OP_LB \<equiv> (32 :: 6 word)\<close>
abbreviation (input) \<open>OP_LH \<equiv> (33 :: 6 word)\<close>
abbreviation (input) \<open>OP_LW \<equiv> (34 :: 6 word)\<close>
abbreviation (input) \<open>OP_LBU \<equiv> (36 :: 6 word)\<close>
abbreviation (input) \<open>OP_LHU \<equiv> (37 :: 6 word)\<close>
abbreviation (input) \<open>OP_SB \<equiv> (40 :: 6 word)\<close>
abbreviation (input) \<open>OP_SH \<equiv> (41 :: 6 word)\<close>
abbreviation (input) \<open>OP_SW \<equiv> (43 :: 6 word)\<close>
abbreviation (input) \<open>ALU_ADD \<equiv> (0 :: 4 word)\<close>
abbreviation (input) \<open>ALU_SUB \<equiv> (1 :: 4 word)\<close>
abbreviation (input) \<open>ALU_SLT \<equiv> (2 :: 4 word)\<close>
abbreviation (input) \<open>ALU_ULT \<equiv> (3 :: 4 word)\<close>
abbreviation (input) \<open>ALU_AND \<equiv> (4 :: 4 word)\<close>
abbreviation (input) \<open>ALU_OR \<equiv> (5 :: 4 word)\<close>
abbreviation (input) \<open>ALU_XOR \<equiv> (6 :: 4 word)\<close>
abbreviation (input) \<open>ALU_NOR \<equiv> (7 :: 4 word)\<close>
abbreviation (input) \<open>SHL \<equiv> (0 :: 2 word)\<close>
abbreviation (input) \<open>LSHR \<equiv> (2 :: 2 word)\<close>
abbreviation (input) \<open>ASHR \<equiv> (3 :: 2 word)\<close>
abbreviation (input) \<open>CondEQ \<equiv> (0 :: 2 word)\<close>
abbreviation (input) \<open>CondNE \<equiv> (1 :: 2 word)\<close>
abbreviation (input) \<open>CondLEZ \<equiv> (2 :: 2 word)\<close>
abbreviation (input) \<open>CondGTZ \<equiv> (3 :: 2 word)\<close>
record regfile_state =
  regfile_r :: \<open>(5 word \<Rightarrow> 32 word)\<close>
definition regfile_out_out1 :: \<open>5 word \<Rightarrow> 5 word \<Rightarrow> 32 word \<Rightarrow> regfile_state \<Rightarrow> 32 word\<close> where
  \<open>regfile_out_out1 ra1 wa in1 \<S> \<equiv> let r = regfile_r \<S> in let out1 = (if (ra1 = (0 :: 5 word)) then (0 :: 32 word) else (if (wa = ra1) then in1 else (r ra1))) in out1\<close>
definition regfile_out_out2 :: \<open>5 word \<Rightarrow> 5 word \<Rightarrow> 32 word \<Rightarrow> regfile_state \<Rightarrow> 32 word\<close> where
  \<open>regfile_out_out2 ra2 wa in1 \<S> \<equiv> let r = regfile_r \<S> in let out2 = (if (ra2 = (0 :: 5 word)) then (0 :: 32 word) else (if (wa = ra2) then in1 else (r ra2))) in out2\<close>
definition regfile_upd :: \<open>5 word \<Rightarrow> 32 word \<Rightarrow> regfile_state \<Rightarrow> regfile_state\<close> where
  \<open>regfile_upd wa in1 \<S> \<equiv> let r = regfile_r \<S> in let r' = if (wa \<noteq> (0 :: 5 word)) then (r(wa := in1)) else r in \<lparr> regfile_r = r' \<rparr>\<close>
record dmem_state =
  dmem_m :: \<open>(12 word \<Rightarrow> 8 word)\<close>
  dmem_out_r :: \<open>32 word\<close>
definition dmem_out_out :: \<open>dmem_state \<Rightarrow> 32 word\<close> where
  \<open>dmem_out_out \<S> \<equiv> let out_r = dmem_out_r \<S> in let out = out_r in out\<close>
definition dmem_upd :: \<open>bool \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow> MemReqSize \<Rightarrow> 32 word \<Rightarrow> dmem_state \<Rightarrow> dmem_state\<close> where
  \<open>dmem_upd en wr addr size1 in1 \<S> \<equiv> let out_r = dmem_out_r \<S> in let m = dmem_m \<S> in let out_r' = if (en \<and> (\<not> wr)) then (case size1 of Byte \<Rightarrow> (word_cat (0 :: 24 word) (m (slice 0 addr :: 12 word)) :: 32 word) | Half \<Rightarrow> (word_cat (0 :: 16 word) (word_cat (m (word_cat (slice 1 addr :: 11 word) (1 :: 1 word) :: 12 word)) (m (word_cat (slice 1 addr :: 11 word) (0 :: 1 word) :: 12 word)) :: 16 word) :: 32 word) | Word \<Rightarrow> (word_cat (m (word_cat (slice 2 addr :: 10 word) (3 :: 2 word) :: 12 word)) (word_cat (m (word_cat (slice 2 addr :: 10 word) (2 :: 2 word) :: 12 word)) (word_cat (m (word_cat (slice 2 addr :: 10 word) (1 :: 2 word) :: 12 word)) (m (word_cat (slice 2 addr :: 10 word) (0 :: 2 word) :: 12 word)) :: 16 word) :: 24 word) :: 32 word)) else out_r in let m' = if (en \<and> wr) then (case size1 of Byte \<Rightarrow> (m((slice 0 addr :: 12 word) := (slice 0 in1 :: 8 word))) | Half \<Rightarrow> ((m((word_cat (slice 1 addr :: 11 word) (0 :: 1 word) :: 12 word) := (slice 0 in1 :: 8 word)))((word_cat (slice 1 addr :: 11 word) (1 :: 1 word) :: 12 word) := (slice 8 in1 :: 8 word))) | Word \<Rightarrow> ((((m((word_cat (slice 2 addr :: 10 word) (0 :: 2 word) :: 12 word) := (slice 0 in1 :: 8 word)))((word_cat (slice 2 addr :: 10 word) (1 :: 2 word) :: 12 word) := (slice 8 in1 :: 8 word)))((word_cat (slice 2 addr :: 10 word) (2 :: 2 word) :: 12 word) := (slice 16 in1 :: 8 word)))((word_cat (slice 2 addr :: 10 word) (3 :: 2 word) :: 12 word) := (slice 24 in1 :: 8 word)))) else m in \<lparr> dmem_m = m', dmem_out_r = out_r' \<rparr>\<close>
definition decode :: \<open>32 word \<Rightarrow> DecodedInst\<close> where
  \<open>decode ir \<equiv> (case ((slice 26 ir :: 6 word), (slice 0 ir :: 6 word)) of (opcode, funct) \<Rightarrow> (case ((if (opcode = (0 :: 6 word)) then (((((((((((((((((((((funct = F_SLLV) \<or> (funct = F_SRLV)) \<or> (funct = F_SRAV)) \<or> (funct = F_JR)) \<or> (funct = F_JALR)) \<or> (funct = F_MTHI)) \<or> (funct = F_MTLO)) \<or> (funct = F_MULT)) \<or> (funct = F_MULTU)) \<or> (funct = F_DIV)) \<or> (funct = F_DIVU)) \<or> (funct = F_ADD)) \<or> (funct = F_ADDU)) \<or> (funct = F_SUB)) \<or> (funct = F_SUBU)) \<or> (funct = F_AND)) \<or> (funct = F_OR)) \<or> (funct = F_XOR)) \<or> (funct = F_NOR)) \<or> (funct = F_SLT)) \<or> (funct = F_SLTU)) else (((((((((((((((((((opcode = OP_BEQ) \<or> (opcode = OP_BNE)) \<or> (opcode = OP_BLEZ)) \<or> (opcode = OP_BGTZ)) \<or> (opcode = OP_ADDI)) \<or> (opcode = OP_ADDIU)) \<or> (opcode = OP_SLTI)) \<or> (opcode = OP_SLTIU)) \<or> (opcode = OP_ANDI)) \<or> (opcode = OP_ORI)) \<or> (opcode = OP_XORI)) \<or> (opcode = OP_LB)) \<or> (opcode = OP_LH)) \<or> (opcode = OP_LW)) \<or> (opcode = OP_LBU)) \<or> (opcode = OP_LHU)) \<or> (opcode = OP_SB)) \<or> (opcode = OP_SH)) \<or> (opcode = OP_SW))), (if (opcode = (0 :: 6 word)) then ((((((((((((((((((((funct = F_SLL) \<or> (funct = F_SRL)) \<or> (funct = F_SRA)) \<or> (funct = F_SLLV)) \<or> (funct = F_SRLV)) \<or> (funct = F_SRAV)) \<or> (funct = F_MULT)) \<or> (funct = F_MULTU)) \<or> (funct = F_DIV)) \<or> (funct = F_DIVU)) \<or> (funct = F_ADD)) \<or> (funct = F_ADDU)) \<or> (funct = F_SUB)) \<or> (funct = F_SUBU)) \<or> (funct = F_AND)) \<or> (funct = F_OR)) \<or> (funct = F_XOR)) \<or> (funct = F_NOR)) \<or> (funct = F_SLT)) \<or> (funct = F_SLTU)) else (((((opcode = OP_BEQ) \<or> (opcode = OP_BNE)) \<or> (opcode = OP_SB)) \<or> (opcode = OP_SH)) \<or> (opcode = OP_SW))), (if (opcode = (0 :: 6 word)) then (((((((((((((((((((funct = F_SLL) \<or> (funct = F_SRL)) \<or> (funct = F_SRA)) \<or> (funct = F_SLLV)) \<or> (funct = F_SRLV)) \<or> (funct = F_SRAV)) \<or> (funct = F_JALR)) \<or> (funct = F_MFHI)) \<or> (funct = F_MFLO)) \<or> (funct = F_ADD)) \<or> (funct = F_ADDU)) \<or> (funct = F_SUB)) \<or> (funct = F_SUBU)) \<or> (funct = F_AND)) \<or> (funct = F_OR)) \<or> (funct = F_XOR)) \<or> (funct = F_NOR)) \<or> (funct = F_SLT)) \<or> (funct = F_SLTU)) else ((((((((((((((opcode = OP_JAL) \<or> (opcode = OP_ADDI)) \<or> (opcode = OP_ADDIU)) \<or> (opcode = OP_SLTI)) \<or> (opcode = OP_SLTIU)) \<or> (opcode = OP_ANDI)) \<or> (opcode = OP_ORI)) \<or> (opcode = OP_XORI)) \<or> (opcode = OP_LUI)) \<or> (opcode = OP_LB)) \<or> (opcode = OP_LH)) \<or> (opcode = OP_LW)) \<or> (opcode = OP_LBU)) \<or> (opcode = OP_LHU)))) of (rd1, rd2, wr) \<Rightarrow> (case ((if rd1 then (slice 21 ir :: 5 word) else (0 :: 5 word)), (if rd2 then (slice 16 ir :: 5 word) else (0 :: 5 word)), (if wr then (if (opcode = (0 :: 6 word)) then (slice 11 ir :: 5 word) else (if (opcode = (3 :: 6 word)) then (31 :: 5 word) else (slice 16 ir :: 5 word))) else (0 :: 5 word)), (slice 0 funct :: 2 word), (if (opcode = (0 :: 6 word)) then (if funct = (32 :: 6 word) \<or> funct = (33 :: 6 word) then ALU_ADD else if funct = (34 :: 6 word) \<or> funct = (35 :: 6 word) then ALU_SUB else if funct = (36 :: 6 word) then ALU_AND else if funct = (37 :: 6 word) then ALU_OR else if funct = (38 :: 6 word) then ALU_XOR else if funct = (39 :: 6 word) then ALU_NOR else if funct = (42 :: 6 word) then ALU_SLT else if funct = (43 :: 6 word) then ALU_ULT else undefined) else (if (opcode = OP_ADDI) then ALU_ADD else (if (opcode = OP_ADDIU) then ALU_ADD else (if (opcode = OP_SLTI) then ALU_SLT else (if (opcode = OP_SLTIU) then ALU_ULT else (if (opcode = OP_ANDI) then ALU_AND else (if (opcode = OP_ORI) then ALU_OR else (if (opcode = OP_XORI) then ALU_XOR else ALU_ADD)))))))), (opcode \<noteq> (0 :: 6 word)), (\<not> (funct !! 2)), (if (opcode = (0 :: 6 word)) then (if ((slice 1 funct :: 5 word) = (4 :: 5 word)) then NextPC_RS else NextPC_NoJump) else (if ((slice 1 opcode :: 5 word) = (1 :: 5 word)) then NextPC_J else (if ((slice 2 opcode :: 4 word) = (1 :: 4 word)) then NextPC_B else NextPC_NoJump))), (slice 0 opcode :: 2 word), (if (((opcode = OP_ANDI) \<or> (opcode = OP_ORI)) \<or> (opcode = OP_XORI)) then ZeroExt else (if (opcode = OP_LUI) then LUI_Ext else SignExt)), (if opcode = OP_LB \<or> opcode = OP_LBU \<or> opcode = OP_LH \<or> opcode = OP_LHU \<or> opcode = OP_LW then True else False), (((opcode = OP_SB) \<or> (opcode = OP_SH)) \<or> (opcode = OP_SW)), (if opcode = OP_LB \<or> opcode = OP_LBU \<or> opcode = OP_SB then Byte else if opcode = OP_LH \<or> opcode = OP_LHU \<or> opcode = OP_SH then Half else if opcode = OP_LW \<or> opcode = OP_SW then Word else undefined), (if opcode = (0 :: 6 word) then (if ((slice 3 funct :: 3 word) = (0 :: 3 word)) then ShifterOut else (if (funct = F_JALR) then PC_plus8 else ALU_Out)) else if opcode = OP_JAL then PC_plus8 else if opcode = OP_ADDI \<or> opcode = OP_ADDIU \<or> opcode = OP_SLTI \<or> opcode = OP_SLTIU \<or> opcode = OP_ANDI \<or> opcode = OP_ORI \<or> opcode = OP_XORI \<or> opcode = OP_LUI then ALU_Out else if opcode = OP_LB \<or> opcode = OP_LBU \<or> opcode = OP_LH \<or> opcode = OP_LHU \<or> opcode = OP_LW then DM_Out else undefined), ((opcode = OP_LB) \<or> (opcode = OP_LH))) of (rf_ra1, rf_ra2, rf_wa, shifter_op, alu_op, alu_b_imm, shamt_imm, next_pc_sel, cond_sel, imm_ext_method, dm_rd, dm_wr, dm_req_size, rf_in_sel, mem_data_sign_ext) \<Rightarrow> \<lparr> DecodedInst_rf_ra1 = rf_ra1, DecodedInst_rf_ra2 = rf_ra2, DecodedInst_rf_wa = rf_wa, DecodedInst_shifter_op = shifter_op, DecodedInst_alu_op = alu_op, DecodedInst_alu_b_imm = alu_b_imm, DecodedInst_shamt_imm = shamt_imm, DecodedInst_next_pc_sel = next_pc_sel, DecodedInst_cond_sel = cond_sel, DecodedInst_imm_ext_method = imm_ext_method, DecodedInst_dm_en = (dm_rd \<or> dm_wr), DecodedInst_dm_wr = dm_wr, DecodedInst_dm_req_size = dm_req_size, DecodedInst_rf_in_sel = rf_in_sel, DecodedInst_mem_data_sign_ext = mem_data_sign_ext \<rparr>)))\<close>
definition alu :: \<open>32 word \<Rightarrow> 32 word \<Rightarrow> 4 word \<Rightarrow> 32 word\<close> where
  \<open>alu a b op \<equiv> (if op = ALU_ADD then (a + b) else if op = ALU_SUB then (a - b) else if op = ALU_SLT then (if (sint a < sint b) then (1 :: 32 word) else (0 :: 32 word)) else if op = ALU_ULT then (if (a < b) then (1 :: 32 word) else (0 :: 32 word)) else if op = ALU_AND then (a AND b) else if op = ALU_OR then (a OR b) else if op = ALU_XOR then (a XOR b) else if op = ALU_NOR then (NOT (a OR b)) else undefined)\<close>
definition shifter :: \<open>32 word \<Rightarrow> 5 word \<Rightarrow> 2 word \<Rightarrow> 32 word\<close> where
  \<open>shifter in1 shamt op \<equiv> (if op = SHL \<or> op = (1 :: 2 word) then (in1 << unat shamt) else if op = LSHR then (in1 >> unat shamt) else if op = ASHR then (in1 >>> unat shamt) else undefined)\<close>
record ExecuteStage =
  ExecuteStage_r1 :: \<open>32 word\<close>
  ExecuteStage_r2 :: \<open>32 word\<close>
  ExecuteStage_imm32 :: \<open>32 word\<close>
  ExecuteStage_rf_wa :: \<open>5 word\<close>
  ExecuteStage_rf_in_sel :: \<open>RegFileInput\<close>
  ExecuteStage_shifter_op :: \<open>2 word\<close>
  ExecuteStage_alu_op :: \<open>4 word\<close>
  ExecuteStage_alu_b_imm :: \<open>bool\<close>
  ExecuteStage_shamt_imm :: \<open>bool\<close>
  ExecuteStage_shamt :: \<open>5 word\<close>
  ExecuteStage_dm_en :: \<open>bool\<close>
  ExecuteStage_dm_wr :: \<open>bool\<close>
  ExecuteStage_dm_req_size :: \<open>MemReqSize\<close>
  ExecuteStage_mem_data_sign_ext :: \<open>bool\<close>
  ExecuteStage_pc :: \<open>30 word\<close>
record MemoryStage =
  MemoryStage_dm_en :: \<open>bool\<close>
  MemoryStage_dm_wr :: \<open>bool\<close>
  MemoryStage_dm_req_size :: \<open>MemReqSize\<close>
  MemoryStage_dm_in :: \<open>32 word\<close>
  MemoryStage_alu_out :: \<open>32 word\<close>
  MemoryStage_shifter_out :: \<open>32 word\<close>
  MemoryStage_rf_wa :: \<open>5 word\<close>
  MemoryStage_rf_in_sel :: \<open>RegFileInput\<close>
  MemoryStage_mem_data_sign_ext :: \<open>bool\<close>
  MemoryStage_pc :: \<open>30 word\<close>
record WritebackStage =
  WritebackStage_alu_out :: \<open>32 word\<close>
  WritebackStage_shifter_out :: \<open>32 word\<close>
  WritebackStage_rf_wa :: \<open>5 word\<close>
  WritebackStage_rf_in_sel :: \<open>RegFileInput\<close>
  WritebackStage_dm_req_size :: \<open>MemReqSize\<close>
  WritebackStage_mem_data_sign_ext :: \<open>bool\<close>
  WritebackStage_pc :: \<open>30 word\<close>
definition rf_in :: \<open>WritebackStage \<Rightarrow> 32 word \<Rightarrow> 32 word\<close> where
  \<open>rf_in wb dm_out \<equiv> (case (WritebackStage_rf_in_sel wb) of ALU_Out \<Rightarrow> (WritebackStage_alu_out wb) | ShifterOut \<Rightarrow> (WritebackStage_shifter_out wb) | DM_Out \<Rightarrow> (case (WritebackStage_dm_req_size wb) of Byte \<Rightarrow> (if (WritebackStage_mem_data_sign_ext wb) then (scast (slice 0 dm_out :: 8 word) :: 32 word) else (ucast (slice 0 dm_out :: 8 word) :: 32 word)) | Half \<Rightarrow> (if (WritebackStage_mem_data_sign_ext wb) then (scast (slice 0 dm_out :: 16 word) :: 32 word) else (ucast (slice 0 dm_out :: 16 word) :: 32 word)) | Word \<Rightarrow> dm_out) | PC_plus8 \<Rightarrow> (word_cat ((WritebackStage_pc wb) + (1 :: 30 word)) (0 :: 2 word) :: 32 word))\<close>
definition next_pc :: \<open>30 word \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow> DecodedInst \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 30 word\<close> where
  \<open>next_pc pc stop inst dinst r1 r2 \<equiv> (case (DecodedInst_next_pc_sel dinst) of NextPC_NoJump \<Rightarrow> (if stop then pc else (pc + (1 :: 30 word))) | NextPC_RS \<Rightarrow> (slice 2 r1 :: 30 word) | NextPC_J \<Rightarrow> (word_cat (slice 26 pc :: 4 word) (slice 0 inst :: 26 word) :: 30 word) | NextPC_B \<Rightarrow> (if (if (DecodedInst_cond_sel dinst) = CondEQ then (r1 = r2) else if (DecodedInst_cond_sel dinst) = CondNE then (r1 \<noteq> r2) else if (DecodedInst_cond_sel dinst) = CondLEZ then (sint r1 \<le> sint (0 :: 32 word)) else if (DecodedInst_cond_sel dinst) = CondGTZ then (sint r1 > sint (0 :: 32 word)) else undefined) then (pc + (scast (slice 0 inst :: 16 word) :: 30 word)) else pc))\<close>
record mips_state =
  mips_pc :: \<open>30 word\<close>
  mips_de_valid :: \<open>bool\<close>
  mips_inst :: \<open>32 word\<close>
  mips_ex :: \<open>ExecuteStage\<close>
  mips_mem :: \<open>MemoryStage\<close>
  mips_wb :: \<open>WritebackStage\<close>
  mips_rf :: \<open>regfile_state\<close>
  mips_dm :: \<open>dmem_state\<close>
definition mips_out_im_en :: \<open>bool \<Rightarrow> mips_state \<Rightarrow> bool\<close> where
  \<open>mips_out_im_en reset \<S> \<equiv> let mem = mips_mem \<S> in let inst = mips_inst \<S> in let ex = mips_ex \<S> in let de_valid = mips_de_valid \<S> in let dinst = (if de_valid then (decode inst) else \<lparr> DecodedInst_rf_ra1 = (0 :: 5 word), DecodedInst_rf_ra2 = (0 :: 5 word), DecodedInst_rf_wa = (0 :: 5 word), DecodedInst_shifter_op = (undefined :: 2 word), DecodedInst_alu_op = (undefined :: 4 word), DecodedInst_alu_b_imm = (undefined :: bool), DecodedInst_shamt_imm = (undefined :: bool), DecodedInst_next_pc_sel = NextPC_NoJump, DecodedInst_cond_sel = (undefined :: 2 word), DecodedInst_imm_ext_method = (undefined :: ImmExtMethod), DecodedInst_dm_en = False, DecodedInst_dm_wr = (undefined :: bool), DecodedInst_dm_req_size = (undefined :: MemReqSize), DecodedInst_rf_in_sel = (undefined :: RegFileInput), DecodedInst_mem_data_sign_ext = (undefined :: bool) \<rparr>) in let stall = (data_hazard (ExecuteStage_rf_wa ex) (MemoryStage_rf_wa mem) (DecodedInst_rf_ra1 dinst) (DecodedInst_rf_ra2 dinst)) in let im_en = (reset \<or> (\<not> stall)) in im_en\<close>
definition mips_out_im_addr :: \<open>mips_state \<Rightarrow> 30 word\<close> where
  \<open>mips_out_im_addr \<S> \<equiv> let pc = mips_pc \<S> in let im_addr = pc in im_addr\<close>
definition mips_upd :: \<open>bool \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow> mips_state \<Rightarrow> mips_state\<close> where
  \<open>mips_upd reset stop im_din \<S> \<equiv> let wb = mips_wb \<S> in let rf = mips_rf \<S> in let pc = mips_pc \<S> in let mem = mips_mem \<S> in let inst = mips_inst \<S> in let ex = mips_ex \<S> in let dm = mips_dm \<S> in let de_valid = mips_de_valid \<S> in let wb' = (if reset then \<lparr> WritebackStage_alu_out = (undefined :: 32 word), WritebackStage_shifter_out = (undefined :: 32 word), WritebackStage_rf_wa = (0 :: 5 word), WritebackStage_rf_in_sel = (undefined :: RegFileInput), WritebackStage_dm_req_size = (undefined :: MemReqSize), WritebackStage_mem_data_sign_ext = (undefined :: bool), WritebackStage_pc = (undefined :: 30 word) \<rparr> else \<lparr> WritebackStage_alu_out = (MemoryStage_alu_out mem), WritebackStage_shifter_out = (MemoryStage_shifter_out mem), WritebackStage_rf_wa = (MemoryStage_rf_wa mem), WritebackStage_rf_in_sel = (MemoryStage_rf_in_sel mem), WritebackStage_dm_req_size = (MemoryStage_dm_req_size mem), WritebackStage_mem_data_sign_ext = (MemoryStage_mem_data_sign_ext mem), WritebackStage_pc = (MemoryStage_pc mem) \<rparr>) in let imm16 = (slice 0 inst :: 16 word) in let shifter_out = (shifter (ExecuteStage_r2 ex) (if (ExecuteStage_shamt_imm ex) then (ExecuteStage_shamt ex) else (slice 0 (ExecuteStage_r1 ex) :: 5 word)) (ExecuteStage_shifter_op ex)) in let alu_out = (alu (ExecuteStage_r1 ex) (if (ExecuteStage_alu_b_imm ex) then (ExecuteStage_imm32 ex) else (ExecuteStage_r2 ex)) (ExecuteStage_alu_op ex)) in let dm_out = dmem_out_out dm in let dm' = dmem_upd (MemoryStage_dm_en mem) (MemoryStage_dm_wr mem) (MemoryStage_alu_out mem) (MemoryStage_dm_req_size mem) (MemoryStage_dm_in mem) dm in let dinst = (if de_valid then (decode inst) else \<lparr> DecodedInst_rf_ra1 = (0 :: 5 word), DecodedInst_rf_ra2 = (0 :: 5 word), DecodedInst_rf_wa = (0 :: 5 word), DecodedInst_shifter_op = (undefined :: 2 word), DecodedInst_alu_op = (undefined :: 4 word), DecodedInst_alu_b_imm = (undefined :: bool), DecodedInst_shamt_imm = (undefined :: bool), DecodedInst_next_pc_sel = NextPC_NoJump, DecodedInst_cond_sel = (undefined :: 2 word), DecodedInst_imm_ext_method = (undefined :: ImmExtMethod), DecodedInst_dm_en = False, DecodedInst_dm_wr = (undefined :: bool), DecodedInst_dm_req_size = (undefined :: MemReqSize), DecodedInst_rf_in_sel = (undefined :: RegFileInput), DecodedInst_mem_data_sign_ext = (undefined :: bool) \<rparr>) in let mem' = (if reset then \<lparr> MemoryStage_dm_en = False, MemoryStage_dm_wr = (undefined :: bool), MemoryStage_dm_req_size = (undefined :: MemReqSize), MemoryStage_dm_in = (undefined :: 32 word), MemoryStage_alu_out = (undefined :: 32 word), MemoryStage_shifter_out = (undefined :: 32 word), MemoryStage_rf_wa = (0 :: 5 word), MemoryStage_rf_in_sel = (undefined :: RegFileInput), MemoryStage_mem_data_sign_ext = (undefined :: bool), MemoryStage_pc = (undefined :: 30 word) \<rparr> else \<lparr> MemoryStage_dm_en = (ExecuteStage_dm_en ex), MemoryStage_dm_wr = (ExecuteStage_dm_wr ex), MemoryStage_dm_req_size = (ExecuteStage_dm_req_size ex), MemoryStage_dm_in = (ExecuteStage_r2 ex), MemoryStage_alu_out = alu_out, MemoryStage_shifter_out = shifter_out, MemoryStage_rf_wa = (ExecuteStage_rf_wa ex), MemoryStage_rf_in_sel = (ExecuteStage_rf_in_sel ex), MemoryStage_mem_data_sign_ext = (ExecuteStage_mem_data_sign_ext ex), MemoryStage_pc = (ExecuteStage_pc ex) \<rparr>) in let rf' = regfile_upd (WritebackStage_rf_wa wb) (rf_in wb dm_out) rf in let stall = (data_hazard (ExecuteStage_rf_wa ex) (MemoryStage_rf_wa mem) (DecodedInst_rf_ra1 dinst) (DecodedInst_rf_ra2 dinst)) in let r2 = regfile_out_out2 (DecodedInst_rf_ra2 dinst) (WritebackStage_rf_wa wb) (rf_in wb dm_out) rf in let r1 = regfile_out_out1 (DecodedInst_rf_ra1 dinst) (WritebackStage_rf_wa wb) (rf_in wb dm_out) rf in let imm32 = (case (DecodedInst_imm_ext_method dinst) of ZeroExt \<Rightarrow> (ucast imm16 :: 32 word) | SignExt \<Rightarrow> (scast imm16 :: 32 word) | LUI_Ext \<Rightarrow> (word_cat imm16 (0 :: 16 word) :: 32 word)) in let inst' = if (\<not> stall) then im_din else inst in let de_valid' = if (reset \<or> (\<not> stall)) then (if reset then False else (((DecodedInst_next_pc_sel dinst) = NextPC_NoJump) \<and> (\<not> stop))) else de_valid in let pc' = if (reset \<or> (\<not> stall)) then (if reset then (0 :: 30 word) else (next_pc pc stop inst dinst r1 r2)) else pc in let ex' = (if reset then \<lparr> ExecuteStage_r1 = (undefined :: 32 word), ExecuteStage_r2 = (undefined :: 32 word), ExecuteStage_imm32 = (undefined :: 32 word), ExecuteStage_rf_wa = (0 :: 5 word), ExecuteStage_rf_in_sel = (undefined :: RegFileInput), ExecuteStage_shifter_op = (undefined :: 2 word), ExecuteStage_alu_op = (undefined :: 4 word), ExecuteStage_alu_b_imm = (undefined :: bool), ExecuteStage_shamt_imm = (undefined :: bool), ExecuteStage_shamt = (undefined :: 5 word), ExecuteStage_dm_en = False, ExecuteStage_dm_wr = (undefined :: bool), ExecuteStage_dm_req_size = (undefined :: MemReqSize), ExecuteStage_mem_data_sign_ext = (undefined :: bool), ExecuteStage_pc = (undefined :: 30 word) \<rparr> else \<lparr> ExecuteStage_r1 = r1, ExecuteStage_r2 = r2, ExecuteStage_imm32 = imm32, ExecuteStage_rf_wa = (if stall then (0 :: 5 word) else (DecodedInst_rf_wa dinst)), ExecuteStage_rf_in_sel = (DecodedInst_rf_in_sel dinst), ExecuteStage_shifter_op = (DecodedInst_shifter_op dinst), ExecuteStage_alu_op = (DecodedInst_alu_op dinst), ExecuteStage_alu_b_imm = (DecodedInst_alu_b_imm dinst), ExecuteStage_shamt_imm = (DecodedInst_shamt_imm dinst), ExecuteStage_shamt = (slice 6 inst :: 5 word), ExecuteStage_dm_en = (if stall then False else (DecodedInst_dm_en dinst)), ExecuteStage_dm_wr = (DecodedInst_dm_wr dinst), ExecuteStage_dm_req_size = (DecodedInst_dm_req_size dinst), ExecuteStage_mem_data_sign_ext = (DecodedInst_mem_data_sign_ext dinst), ExecuteStage_pc = pc \<rparr>) in \<lparr> mips_pc = pc', mips_de_valid = de_valid', mips_inst = inst', mips_ex = ex', mips_mem = mem', mips_wb = wb', mips_rf = rf', mips_dm = dm' \<rparr>\<close>
end
