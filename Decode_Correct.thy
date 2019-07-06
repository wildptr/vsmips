theory Decode_Correct imports MIPS MIPS_Model begin

primrec not_jb :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>not_jb (Inst_ALU_R _ _ _ _) = True\<close> |
  \<open>not_jb (Inst_ALU_I _ _ _ _) = True\<close> |
  \<open>not_jb (Inst_Shift_R _ _ _ _) = True\<close> |
  \<open>not_jb (Inst_Shift_I _ _ _ _) = True\<close> |
  \<open>not_jb (Inst_LUI _ _) = True\<close> |
  \<open>not_jb (Inst_J _) = False\<close> |
  \<open>not_jb (Inst_JAL _) = False\<close> |
  \<open>not_jb (Inst_JR _) = False\<close> |
  \<open>not_jb (Inst_JALR _ _) = False\<close> |
  \<open>not_jb (Inst_Branch _ _ _ _) = False\<close> |
  \<open>not_jb (Inst_Branch1 _ _ _) = False\<close> |
  \<open>not_jb (Inst_Load _ _ _ _ _) = True\<close> |
  \<open>not_jb (Inst_Store _ _ _ _) = True\<close> |
  \<open>not_jb Inst_Undef = False\<close>

lemma decode_not_jb_next_pc_sel:
  \<open>not_jb (mips.decode inst) \<Longrightarrow> DecodedInst_next_pc_sel (decode inst) = NextPC_NoJump\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun is_jump_imm :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>is_jump_imm (Inst_J _) = True\<close> |
  \<open>is_jump_imm (Inst_JAL _) = True\<close> |
  \<open>is_jump_imm _ = False\<close>

lemma decode_jump_imm_pc_sel:
  \<open>is_jump_imm (mips.decode inst) \<Longrightarrow> DecodedInst_next_pc_sel (decode inst) = NextPC_J\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun is_jump_reg :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>is_jump_reg (Inst_JR _) = True\<close> |
  \<open>is_jump_reg (Inst_JALR _ _) = True\<close> |
  \<open>is_jump_reg _ = False\<close>

lemma decode_jump_reg_pc_sel:
  \<open>is_jump_reg (mips.decode inst) \<Longrightarrow> DecodedInst_next_pc_sel (decode inst) = NextPC_RS\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun br_cond :: \<open>inst \<Rightarrow> 2 word option\<close> where
  \<open>br_cond (Inst_Branch EQ _ _ _) = Some CondEQ\<close> |
  \<open>br_cond (Inst_Branch NE _ _ _) = Some CondNE\<close> |
  \<open>br_cond (Inst_Branch1 LEZ _ _) = Some CondLEZ\<close> |
  \<open>br_cond (Inst_Branch1 GTZ _ _) = Some CondGTZ\<close> |
  \<open>br_cond _ = None\<close>

lemma decode_br_pc_sel:
  \<open>br_cond (mips.decode inst) = Some cond \<Longrightarrow> DecodedInst_next_pc_sel (decode inst) = NextPC_B\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_cond_sel:
  \<open>br_cond (mips.decode inst) = Some cond \<Longrightarrow> DecodedInst_cond_sel (decode inst) = cond\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

primrec not_ls :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>not_ls (Inst_ALU_R _ _ _ _) = True\<close> |
  \<open>not_ls (Inst_ALU_I _ _ _ _) = True\<close> |
  \<open>not_ls (Inst_Shift_R _ _ _ _) = True\<close> |
  \<open>not_ls (Inst_Shift_I _ _ _ _) = True\<close> |
  \<open>not_ls (Inst_LUI _ _) = True\<close> |
  \<open>not_ls (Inst_J _) = True\<close> |
  \<open>not_ls (Inst_JAL _) = True\<close> |
  \<open>not_ls (Inst_JR _) = True\<close> |
  \<open>not_ls (Inst_JALR _ _) = True\<close> |
  \<open>not_ls (Inst_Branch _ _ _ _) = True\<close> |
  \<open>not_ls (Inst_Branch1 _ _ _) = True\<close> |
  \<open>not_ls (Inst_Load _ _ _ _ _) = False\<close> |
  \<open>not_ls (Inst_Store _ _ _ _) = False\<close> |
  \<open>not_ls Inst_Undef = False\<close>

fun is_ls :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>is_ls (Inst_Load _ _ _ _ _) = True\<close> |
  \<open>is_ls (Inst_Store _ _ _ _) = True\<close> |
  \<open>is_ls _ = False\<close>

lemma decode_not_ls_dm_en:
  \<open>not_ls (mips.decode inst) \<Longrightarrow> \<not> DecodedInst_dm_en (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_ls_dm_en:
  \<open>is_ls (mips.decode inst) \<Longrightarrow> DecodedInst_dm_en (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

primrec read_rs :: \<open>inst \<Rightarrow> 5 word\<close> where
  \<open>read_rs (Inst_ALU_R op rd rs rt) = rs\<close> |
  \<open>read_rs (Inst_ALU_I op rd rs imm) = rs\<close> |
  \<open>read_rs (Inst_Shift_R op rd rt rs) = rs\<close> |
  \<open>read_rs (Inst_Shift_I op rd rt shamt) = 0\<close> |
  \<open>read_rs (Inst_LUI _ _) = 0\<close> |
  \<open>read_rs (Inst_J _) = 0\<close> |
  \<open>read_rs (Inst_JAL _) = 0\<close> |
  \<open>read_rs (Inst_JR rs) = rs\<close> |
  \<open>read_rs (Inst_JALR rd rs) = rs\<close> |
  \<open>read_rs (Inst_Branch op rs rt imm) = rs\<close> |
  \<open>read_rs (Inst_Branch1 op rs imm) = rs\<close> |
  \<open>read_rs (Inst_Load sz sign rt rs imm) = rs\<close> |
  \<open>read_rs (Inst_Store sz rt rs imm) = rs\<close> |
  \<open>read_rs Inst_Undef = undefined\<close>

lemma decode_rf_ra1:
  \<open>mips.decode inst \<noteq> Inst_Undef \<Longrightarrow> read_rs (mips.decode inst) = rs \<Longrightarrow> DecodedInst_rf_ra1 (decode inst) = rs\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

primrec read_rt :: \<open>inst \<Rightarrow> 5 word\<close> where
  \<open>read_rt (Inst_ALU_R op rd rs rt) = rt\<close> |
  \<open>read_rt (Inst_ALU_I op rd rs imm) = 0\<close> |
  \<open>read_rt (Inst_Shift_R op rd rt rs) = rt\<close> |
  \<open>read_rt (Inst_Shift_I op rd rt shamt) = rt\<close> |
  \<open>read_rt (Inst_LUI _ _) = 0\<close> |
  \<open>read_rt (Inst_J _) = 0\<close> |
  \<open>read_rt (Inst_JAL _) = 0\<close> |
  \<open>read_rt (Inst_JR rs) = 0\<close> |
  \<open>read_rt (Inst_JALR rd rs) = 0\<close> |
  \<open>read_rt (Inst_Branch op rs rt imm) = rt\<close> |
  \<open>read_rt (Inst_Branch1 op rs imm) = 0\<close> |
  \<open>read_rt (Inst_Load sz sign rt rs imm) = 0\<close> |
  \<open>read_rt (Inst_Store sz rt rs imm) = rt\<close> |
  \<open>read_rt Inst_Undef = undefined\<close>

lemma decode_rf_ra2:
  \<open>mips.decode inst \<noteq> Inst_Undef \<Longrightarrow> read_rt (mips.decode inst) = rt \<Longrightarrow> DecodedInst_rf_ra2 (decode inst) = rt\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

primrec write_r :: \<open>inst \<Rightarrow> 5 word\<close> where
  \<open>write_r (Inst_ALU_R op rd rs rt) = rd\<close> |
  \<open>write_r (Inst_ALU_I op rd rs imm) = rd\<close> |
  \<open>write_r (Inst_Shift_R op rd rt rs) = rd\<close> |
  \<open>write_r (Inst_Shift_I op rd rt shamt) = rd\<close> |
  \<open>write_r (Inst_LUI rd imm) = rd\<close> |
  \<open>write_r (Inst_J imm) = 0\<close> |
  \<open>write_r (Inst_JAL imm) = 31\<close> |
  \<open>write_r (Inst_JR rs) = 0\<close> |
  \<open>write_r (Inst_JALR rd rs) = rd\<close> |
  \<open>write_r (Inst_Branch op rs rt imm) = 0\<close> |
  \<open>write_r (Inst_Branch1 op rs imm) = 0\<close> |
  \<open>write_r (Inst_Load sz sign rt rs imm) = rt\<close> |
  \<open>write_r (Inst_Store sign rt rs imm) = 0\<close> |
  \<open>write_r Inst_Undef = undefined\<close>

lemma decode_rf_wa:
  \<open>mips.decode inst \<noteq> Inst_Undef \<Longrightarrow> write_r (mips.decode inst) = r \<Longrightarrow> DecodedInst_rf_wa (decode inst) = r\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

primrec convert_alu_op :: \<open>ALU_op \<Rightarrow> 4 word\<close> where
  \<open>convert_alu_op OP_ADD  = ALU_ADD\<close> |
  \<open>convert_alu_op OP_SUB  = ALU_SUB\<close> |
  \<open>convert_alu_op OP_AND  = ALU_AND\<close> |
  \<open>convert_alu_op OP_OR   = ALU_OR \<close> |
  \<open>convert_alu_op OP_XOR  = ALU_XOR\<close> |
  \<open>convert_alu_op OP_NOR  = ALU_NOR\<close> |
  \<open>convert_alu_op OP_SLT  = ALU_SLT\<close> |
  \<open>convert_alu_op OP_SLTU = ALU_ULT\<close>

fun alu_op :: \<open>inst \<Rightarrow> ALU_op option\<close> where
  \<open>alu_op (Inst_ALU_R op _ _ _) = Some op\<close> |
  \<open>alu_op (Inst_ALU_I op _ _ _) = Some op\<close> |
  \<open>alu_op (Inst_LUI _ _) = Some OP_ADD\<close> | (* could be any op satisfying \<open>0 \<oplus> x = x\<close> *)
  \<open>alu_op (Inst_Load _ _ _ _ _) = Some OP_ADD\<close> |
  \<open>alu_op (Inst_Store _ _ _ _) = Some OP_ADD\<close> |
  \<open>alu_op _ = None\<close>

fun shifter_op :: \<open>inst \<Rightarrow> shift_op option\<close> where
  \<open>shifter_op (Inst_Shift_R op _ _ _) = Some op\<close> |
  \<open>shifter_op (Inst_Shift_I op _ _ _) = Some op\<close> |
  \<open>shifter_op _ = None\<close>

fun rf_in_is_alu_out where
  \<open>rf_in_is_alu_out (Inst_ALU_R _ _ _ _) = True\<close> |
  \<open>rf_in_is_alu_out (Inst_ALU_I _ _ _ _) = True\<close> |
  \<open>rf_in_is_alu_out (Inst_LUI _ _) = True\<close> |
  \<open>rf_in_is_alu_out _ = False\<close>

lemma decode_alu_rf_in_sel:
  \<open>rf_in_is_alu_out (mips.decode inst) \<Longrightarrow> DecodedInst_rf_in_sel (decode inst) = ALU_Out\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_shifter_rf_in_sel:
  \<open>shifter_op (mips.decode inst) = Some op \<Longrightarrow> DecodedInst_rf_in_sel (decode inst) = ShifterOut\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_load_rf_in_sel:
  \<open>mips.decode inst = Inst_Load sz sign rt rs imm \<Longrightarrow> DecodedInst_rf_in_sel (decode inst) = DM_Out\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_alu_op:
  \<open>alu_op (mips.decode inst) = Some op \<Longrightarrow> DecodedInst_alu_op (decode inst) = convert_alu_op op\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_ALU_R_alu_b_imm:
  \<open>mips.decode inst = Inst_ALU_R op rd rs rt \<Longrightarrow> \<not> DecodedInst_alu_b_imm (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def Let_def)
  by unat_arith

fun alu_b_imm :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>alu_b_imm (Inst_ALU_I _ _ _ _) = True\<close> |
  \<open>alu_b_imm (Inst_LUI _ _) = True\<close> |
  \<open>alu_b_imm (Inst_Load _ _ _ _ _) = True\<close> |
  \<open>alu_b_imm (Inst_Store _ _ _ _) = True\<close> |
  \<open>alu_b_imm _ = False\<close>

lemma decode_alu_b_imm:
  \<open>alu_b_imm (mips.decode inst) \<Longrightarrow> DecodedInst_alu_b_imm (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def Let_def)
  by unat_arith

primrec convert_shift_op :: \<open>shift_op \<Rightarrow> 2 word\<close> where
  \<open>convert_shift_op OP_SLL = SHL\<close> |
  \<open>convert_shift_op OP_SRL = LSHR\<close> |
  \<open>convert_shift_op OP_SRA = ASHR\<close>

lemma decode_shifter_op:
  \<open>shifter_op (mips.decode inst) = Some op \<Longrightarrow> DecodedInst_shifter_op (decode inst) = convert_shift_op op\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_ALU_I_bitwise_imm_ext_method:
  \<open>mips.decode inst = Inst_ALU_I op rt rs imm \<Longrightarrow> is_bitwise_op op \<Longrightarrow> DecodedInst_imm_ext_method (decode inst) = ZeroExt\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_ALU_I_non_bitwise_imm_ext_method:
  \<open>mips.decode inst = Inst_ALU_I op rt rs imm \<Longrightarrow> \<not> is_bitwise_op op \<Longrightarrow> DecodedInst_imm_ext_method (decode inst) = SignExt\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  done

lemma decode_LUI_imm_ext_method:
  \<open>mips.decode inst = Inst_LUI rt imm \<Longrightarrow> DecodedInst_imm_ext_method (decode inst) = LUI_Ext\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun get_imm16 :: \<open>inst \<Rightarrow> 16 word option\<close> where
  \<open>get_imm16 (Inst_ALU_I op rd rs imm) = Some imm\<close> |
  \<open>get_imm16 (Inst_Branch op rs rt imm) = Some imm\<close> |
  \<open>get_imm16 (Inst_Branch1 op rs imm) = Some imm\<close> |
  \<open>get_imm16 (Inst_LUI rt imm) = Some imm\<close> |
  \<open>get_imm16 (Inst_Load _ _ _ _ imm) = Some imm\<close> |
  \<open>get_imm16 (Inst_Store _ _ _ imm) = Some imm\<close> |
  \<open>get_imm16 _ = None\<close>

lemma decode_imm16:
  \<open>get_imm16 (mips.decode inst) = Some imm \<Longrightarrow> ucast inst = imm\<close>
  apply(simp add: mips.decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_Shift_I_shamt_imm:
  \<open>mips.decode inst = Inst_Shift_I op rd rt shamt \<Longrightarrow> DecodedInst_shamt_imm (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_Shift_I_shamt:
  \<open>mips.decode inst = Inst_Shift_I op rd rt shamt \<Longrightarrow> slice 6 inst = shamt\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_Shift_R_shamt_imm:
  \<open>mips.decode inst = Inst_Shift_R op rd rt rs \<Longrightarrow> \<not> DecodedInst_shamt_imm (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun is_jr :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>is_jr (Inst_JR _) = True\<close> |
  \<open>is_jr (Inst_JALR _ _) = True\<close> |
  \<open>is_jr _ = False\<close>

lemma decode_jr_next_pc_sel:
  \<open>is_jr (mips.decode inst) \<Longrightarrow> DecodedInst_next_pc_sel (decode inst) = NextPC_RS\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun is_jal :: \<open>inst \<Rightarrow> bool\<close> where
  \<open>is_jal (Inst_JAL _) = True\<close> |
  \<open>is_jal (Inst_JALR _ _) = True\<close> |
  \<open>is_jal _ = False\<close>

lemma decode_jal_rf_in_sel:
  \<open>is_jal (mips.decode inst) \<Longrightarrow> DecodedInst_rf_in_sel (decode inst) = PC_plus8\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

fun get_imm26 :: \<open>inst \<Rightarrow> 26 word option\<close> where
  \<open>get_imm26 (Inst_J imm) = Some imm\<close> |
  \<open>get_imm26 (Inst_JAL imm) = Some imm\<close> |
  \<open>get_imm26 _ = None\<close>

lemma decode_imm26:
  \<open>get_imm26 (mips.decode inst) = Some imm \<Longrightarrow> ucast inst = imm\<close>
  apply(simp add: mips.decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

primrec convert_mem_req_size where
  \<open>convert_mem_req_size BYTE = Byte\<close> |
  \<open>convert_mem_req_size HALF = Half\<close> |
  \<open>convert_mem_req_size WORD = Word\<close>

fun ls_size where
  \<open>ls_size (Inst_Load sz _ _ _ _) = Some sz\<close> |
  \<open>ls_size (Inst_Store sz _ _ _) = Some sz\<close> |
  \<open>ls_size _ = None\<close>

lemma decode_dm_req_size:
  \<open>ls_size (mips.decode inst) = Some sz \<Longrightarrow> DecodedInst_dm_req_size (decode inst) = convert_mem_req_size sz\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

term DecodedInst_dm_ext_sign
lemma decode_mem_data_sign_ext:
  \<open>mips.decode inst = Inst_Load sz sign rt rs imm \<Longrightarrow> DecodedInst_mem_data_sign_ext (decode inst) = sign\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_load_dm_wr:
  \<open>mips.decode inst = Inst_Load sz sign rt rs imm \<Longrightarrow> \<not> DecodedInst_dm_wr (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_store_dm_wr:
  \<open>mips.decode inst = Inst_Store sz rt rs imm \<Longrightarrow> DecodedInst_dm_wr (decode inst)\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0 :: 6 word)\<close>; simp)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 2\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 3\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 4\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 6\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 7\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 8\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 9\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x20\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x21\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x22\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x23\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x24\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x25\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x26\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x27\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2a\<close>; simp add: ucast_slice)
   apply(cases \<open>UCAST(32\<rightarrow>6) inst = 0x2b\<close>; simp add: ucast_slice)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (32::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (33::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (34::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (36::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (37::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (40::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (41::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (43::6 word)\<close>; simp)
  done

lemma decode_ls_imm_ext_method:
  \<open>is_ls (mips.decode inst) \<Longrightarrow> DecodedInst_imm_ext_method (decode inst) = SignExt\<close>
  apply(simp add: mips.decode_def decode_def)
  apply(cases \<open>slice 26 inst = (0::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (2::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (3::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (4::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (5::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (6::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (7::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (8::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (9::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (10::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (11::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (12::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (13::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (14::6 word)\<close>; simp)
  apply(cases \<open>slice 26 inst = (15::6 word)\<close>; simp)
  done

end
