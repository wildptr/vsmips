theory MIPS_Correctness imports MIPS_Model MIPS Decode_Correct begin

definition ex_empty :: \<open>mips_state \<Rightarrow> bool\<close> where
  \<open>ex_empty s \<equiv> let ex = mips_ex s in \<not> ExecuteStage_dm_en ex \<and> ExecuteStage_rf_wa ex = 0\<close>

definition mem_empty :: \<open>mips_state \<Rightarrow> bool\<close> where
  \<open>mem_empty s \<equiv> let mem = mips_mem s in \<not> MemoryStage_dm_en mem \<and> MemoryStage_rf_wa mem = 0\<close>

definition wb_empty :: \<open>mips_state \<Rightarrow> bool\<close> where
  \<open>wb_empty s \<equiv> WritebackStage_rf_wa (mips_wb s) = 0\<close>

declare ex_empty_def[simp] mem_empty_def[simp] wb_empty_def[simp]

definition flushed :: \<open>mips_state \<Rightarrow> bool\<close> where
  \<open>flushed s \<equiv> \<not> mips_de_valid s \<and> ex_empty s \<and> mem_empty s \<and> wb_empty s\<close>

lemma reset_state_is_flushed:
  \<open>flushed (mips_upd True stop im_data s)\<close>
  by (simp add: flushed_def mips_upd_def Let_def)

lemma flushed1_flushed_aux:
  \<open>flushed s \<Longrightarrow> flushed (mips_upd False True im_data s)\<close>
  by (simp add: flushed_def mips_upd_def Let_def)

definition stall :: \<open>mips_state \<Rightarrow> bool\<close> where
  \<open>stall s \<equiv>
     case
       (if mips_de_valid s
          then let dinst = decode (mips_inst s) in (DecodedInst_rf_ra1 dinst, DecodedInst_rf_ra2 dinst)
          else (0, 0))
     of (de_ra1, de_ra2) \<Rightarrow>
     let ex_wa = ExecuteStage_rf_wa (mips_ex s) in
     let mem_wa = MemoryStage_rf_wa (mips_mem s) in
   data_hazard ex_wa mem_wa de_ra1 de_ra2\<close>

lemma
  \<open>flushed s \<Longrightarrow> \<not> stall s\<close>
  by (simp add: flushed_def stall_def Let_def data_hazard_def eqnz_def)

definition flush1 :: \<open>mips_state \<Rightarrow> mips_state\<close> where
  \<open>flush1 s \<equiv> mips_upd False True undefined s\<close>

lemma flush1_flushed:
  \<open>flushed s \<Longrightarrow> flushed (flush1 s)\<close>
  apply(simp add: flush1_def)
  by (rule flushed1_flushed_aux)

definition flush_till_ex :: \<open>mips_state \<Rightarrow> mips_state\<close> where
  \<open>flush_till_ex s \<equiv> flush1 (flush1 (flush1 s))\<close>

lemma flush_till_ex_correct:
  \<open>\<not> mips_de_valid s \<Longrightarrow> flushed (flush_till_ex s)\<close>
  by (simp add: flushed_def flush_till_ex_def flush1_def Let_def mips_upd_def)

lemma stall_imp_next_ex_empty:
  \<open>stall s \<Longrightarrow> ex_empty (flush1 s)\<close>
  by (auto simp add: stall_def flush1_def mips_upd_def Let_def)

lemma de_empty_imp_next_ex_empty:
  \<open>\<not> mips_de_valid s \<Longrightarrow> ex_empty (flush1 s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma stall_and_ex_empty_imp_next_mem_empty:
  \<open>stall s \<Longrightarrow> ex_empty s \<Longrightarrow> mem_empty (flush1 s)\<close>
  by (simp add: stall_def flush1_def mips_upd_def Let_def)

lemma ex_and_mem_empty_imp_no_stall:
  \<open>ex_empty s \<Longrightarrow> mem_empty s \<Longrightarrow> \<not> stall s\<close>
  by (simp add: stall_def data_hazard_def eqnz_def Let_def)

lemma de_empty_imp_no_stall:
  \<open>\<not> mips_de_valid s \<Longrightarrow> \<not> stall s\<close>
  by (simp add: stall_def data_hazard_def eqnz_def)

lemma no_stall_imp_next_de_empty:
  \<open>\<not> stall s \<Longrightarrow> \<not> mips_de_valid (flush1 s)\<close>
  by (auto simp add: stall_def data_hazard_def eqnz_def Let_def flush1_def mips_upd_def)

(* lemma de_empty_imp_next_de_empty:
  \<open>\<not> mips_de_valid s \<Longrightarrow> \<not> mips_de_valid (flush1 s)\<close>
  using no_stall_imp_next_de_empty de_empty_imp_no_stall by blast *)

definition run_until_no_stall :: \<open>mips_state \<Rightarrow> mips_state\<close> where
  \<open>run_until_no_stall s \<equiv>
     if stall s then
       let s1 = flush1 s in \<comment> \<open>ex_empty s1\<close>
       if stall s1 then
         flush1 s1
       else s1
     else s\<close>

lemma run_until_no_stall_correct:
  \<open>\<not> stall (run_until_no_stall s)\<close>
  apply(auto simp add: run_until_no_stall_def Let_def)
  apply(subgoal_tac \<open>ex_empty (flush1 s)\<close>)
   apply(subgoal_tac \<open>ex_empty (flush1 (flush1 s))\<close>)
    apply(subgoal_tac \<open>mem_empty (flush1 (flush1 s))\<close>)
  using ex_and_mem_empty_imp_no_stall[of \<open>flush1 (flush1 s)\<close>] apply blast
    apply(erule stall_and_ex_empty_imp_next_mem_empty)
    apply assumption
  using stall_imp_next_ex_empty apply blast+
  done

definition flush :: \<open>mips_state \<Rightarrow> mips_state\<close> where
  \<open>flush s \<equiv> if \<not> mips_de_valid s then flush_till_ex s else flush_till_ex (flush1 (run_until_no_stall s))\<close>

lemma flush_correct:
  \<open>flushed (flush s)\<close>
  apply(auto simp add: flush_def)
   apply(fact flush_till_ex_correct)
  apply(subgoal_tac \<open>\<not> mips_de_valid (flush1 (run_until_no_stall s))\<close>)
   apply(erule flush_till_ex_correct)
  apply(subgoal_tac \<open>\<not> stall (run_until_no_stall s)\<close>)
   apply(erule no_stall_imp_next_de_empty)
  apply(rule run_until_no_stall_correct)
  done

lemma flush_de_empty:
  \<open>\<not> mips_de_valid s \<Longrightarrow> flush s = flush_till_ex s\<close>
  by (simp add: flush_def)

type_synonym dmem = \<open>12 word \<Rightarrow> 8 word\<close>

definition proj :: \<open>mips_state \<Rightarrow> dmem isa_state\<close> where
  \<open>proj s = \<lparr> PC = mips_pc s, Regs = regfile_r (mips_rf s), Mem = dmem_m (mips_dm s) \<rparr>\<close>
definition abstract :: \<open>mips_state \<Rightarrow> (12 word \<Rightarrow> 8 word) isa_state\<close> where
  \<open>abstract s \<equiv> proj (flush s)\<close>

(* inductive is_initial :: \<open>mips_state \<Rightarrow> bool\<close> where
  is_initialI: \<open>is_initial (mips_upd True stop im_data s)\<close> *)

lemma flush1_same_proj:
  \<open>flushed s \<Longrightarrow> proj s = proj (flush1 s)\<close>
  by (simp add: proj_def Let_def flush1_def flushed_def mips_upd_def regfile_upd_def dmem_upd_def next_pc_def)

definition impl_step :: \<open>(30 word \<Rightarrow> 32 word) \<Rightarrow> mips_state \<Rightarrow> mips_state\<close> where
  \<open>impl_step im s \<equiv> mips_upd False False (im (mips_out_im_addr s)) s\<close>

definition load :: \<open>32 word \<Rightarrow> mem_req_size \<Rightarrow> (12 word \<Rightarrow> 8 word) \<Rightarrow> 32 word\<close> where
  \<open>load addr sz m \<equiv>
     case sz of
       BYTE \<Rightarrow> ucast (m (ucast addr)) |
       HALF \<Rightarrow>
         let addr_base = slice 1 addr :: 11 word in
         let b0 = m (word_cat addr_base (0::1 word)) in
         let b1 = m (word_cat addr_base (1::1 word)) in
         ucast (word_cat b1 b0 :: 16 word) |
       WORD \<Rightarrow>
         let addr_base = slice 2 addr :: 10 word in
         let b0 = m (word_cat addr_base (0::2 word)) in
         let b1 = m (word_cat addr_base (1::2 word)) in
         let b2 = m (word_cat addr_base (2::2 word)) in
         let b3 = m (word_cat addr_base (3::2 word)) in
         word_cat b3 (word_cat b2 (word_cat b1 b0 :: 16 word) :: 24 word)\<close>

definition store :: \<open>32 word \<Rightarrow> mem_req_size \<Rightarrow> 32 word \<Rightarrow> (12 word \<Rightarrow> 8 word) \<Rightarrow> (12 word \<Rightarrow> 8 word)\<close> where
  \<open>store addr sz data m \<equiv>
     case sz of
       BYTE \<Rightarrow> m(ucast addr := ucast data) |
       HALF \<Rightarrow>
         let addr_base = slice 1 addr :: 11 word in
         (m(word_cat addr_base (0::1 word) := ucast data))
           (word_cat addr_base (1::1 word) := slice 8 data) |
       WORD \<Rightarrow>
         let addr_base = slice 2 addr :: 10 word in
         (((m(word_cat addr_base (0::2 word) := ucast data))
             (word_cat addr_base (1::2 word) := slice 8 data))
             (word_cat addr_base (2::2 word) := slice 16 data))
             (word_cat addr_base (3::2 word) := slice 24 data)\<close>

(*
lemma \<open>(word_cat (0b1101::4 word) (0b01::2 word) :: 6 word) = 0b110101\<close>
  by (simp add: word_cat_def bin_cat_def)
*)

lemma de_invalid_to_de_valid:
  \<open>s1 = impl_step im s0 \<Longrightarrow> \<not> mips_de_valid s0 \<Longrightarrow> mips_de_valid s1\<close>
  by (simp add: impl_step_def mips_upd_def Let_def data_hazard_def eqnz_def)

lemma a1:
  \<open>mips_ex  (flush1 s) = mips_ex  (impl_step im s) \<and>
   mips_mem (flush1 s) = mips_mem (impl_step im s) \<and>
   mips_wb  (flush1 s) = mips_wb  (impl_step im s)\<close>
  by (simp add: flush1_def impl_step_def mips_upd_def data_hazard_def eqnz_def Let_def)

lemma a2:
  \<open>\<not> mips_de_valid (impl_step im s) \<Longrightarrow> mips_pc (flush1 s) = mips_pc (impl_step im s)\<close>
  by (auto simp add: flush1_def impl_step_def mips_upd_def Let_def next_pc_def;
      simp add: data_hazard_def eqnz_def;
      cases \<open>DecodedInst_next_pc_sel (decode (mips_inst s))\<close>; simp)

lemma a3:
  \<open>mips_rf (flush1 s) = mips_rf (impl_step im s)\<close>
  by (simp add: flush1_def impl_step_def mips_upd_def data_hazard_def eqnz_def Let_def)

lemma a4:
  \<open>mips_dm (flush1 s) = mips_dm (impl_step im s)\<close>
  by (simp add: flush1_def impl_step_def mips_upd_def data_hazard_def eqnz_def Let_def)

lemma b1:
  \<open>mips_pc s1 = mips_pc s2 \<Longrightarrow>
   mips_rf s1 = mips_rf s2 \<Longrightarrow>
   mips_dm s1 = mips_dm s2 \<Longrightarrow>
   \<not> mips_de_valid s1 \<Longrightarrow> \<not> mips_de_valid s2 \<Longrightarrow>
   mips_ex s1 = mips_ex s2 \<Longrightarrow> mips_mem s1 = mips_mem s2 \<Longrightarrow> mips_wb s1 = mips_wb s2 \<Longrightarrow>
   s1' = flush1 s1 \<Longrightarrow> s2' = flush1 s2 \<Longrightarrow>
   mips_pc s1' = mips_pc s2' \<and>
   mips_rf s1' = mips_rf s2' \<and>
   mips_dm s1' = mips_dm s2' \<and>
   \<not> mips_de_valid s1' \<and> \<not> mips_de_valid s2' \<and>
   ex_empty s1' \<and> ex_empty s2' \<and> mips_mem s1' = mips_mem s2' \<and> mips_wb s1' = mips_wb s2'\<close>
  by (auto simp add: flush1_def mips_upd_def Let_def next_pc_def)

lemma b2:
  \<open>mips_pc s1 = mips_pc s2 \<Longrightarrow>
   mips_rf s1 = mips_rf s2 \<Longrightarrow>
   mips_dm s1 = mips_dm s2 \<Longrightarrow>
   \<not> mips_de_valid s1 \<Longrightarrow> \<not> mips_de_valid s2 \<Longrightarrow>
   ex_empty s1 \<and> ex_empty s2 \<Longrightarrow> mips_mem s1 = mips_mem s2 \<Longrightarrow> mips_wb s1 = mips_wb s2 \<Longrightarrow>
   s1' = flush1 s1 \<Longrightarrow> s2' = flush1 s2 \<Longrightarrow>
   mips_pc s1' = mips_pc s2' \<and>
   mips_rf s1' = mips_rf s2' \<and>
   mips_dm s1' = mips_dm s2' \<and>
   \<not> mips_de_valid s1' \<and> \<not> mips_de_valid s2' \<and>
   ex_empty s1' \<and> ex_empty s2' \<and> mem_empty s1' \<and> mem_empty s2' \<and> mips_wb s1' = mips_wb s2'\<close>
  by (auto simp add: flush1_def mips_upd_def Let_def next_pc_def)

lemma b3:
  \<open>mips_pc s1 = mips_pc s2 \<Longrightarrow>
   mips_rf s1 = mips_rf s2 \<Longrightarrow>
   mips_dm s1 = mips_dm s2 \<Longrightarrow>
   \<not> mips_de_valid s1 \<Longrightarrow> \<not> mips_de_valid s2 \<Longrightarrow>
   ex_empty s1 \<and> ex_empty s2 \<Longrightarrow> mem_empty s1 \<and> mem_empty s2 \<Longrightarrow> mips_wb s1 = mips_wb s2 \<Longrightarrow>
   s1' = flush1 s1 \<Longrightarrow> s2' = flush1 s2 \<Longrightarrow>
   mips_pc s1' = mips_pc s2' \<and>
   mips_rf s1' = mips_rf s2' \<and>
   mips_dm s1' = mips_dm s2' \<and>
   \<not> mips_de_valid s1' \<and> \<not> mips_de_valid s2' \<and>
   ex_empty s1' \<and> ex_empty s2' \<and> mem_empty s1' \<and> mem_empty s2' \<and> wb_empty s1' \<and> wb_empty s2'\<close>
  by (auto simp add: flush1_def mips_upd_def Let_def dmem_upd_def next_pc_def)

definition mips_state_sim :: \<open>mips_state \<Rightarrow> mips_state \<Rightarrow> bool\<close> where
  \<open>mips_state_sim s1 s2 \<equiv>
     mips_pc s1 = mips_pc s2 \<and> mips_rf s1 = mips_rf s2 \<and> mips_dm s1 = mips_dm s2 \<and>
     (\<not> mips_de_valid s1 \<and> \<not> mips_de_valid s2 \<or> mips_de_valid s1 \<and> mips_de_valid s2 \<and> mips_inst s1 = mips_inst s2) \<and>
     (ex_empty s1 \<and> ex_empty s2 \<or> mips_ex s1 = mips_ex s2) \<and>
     (mem_empty s1 \<and> mem_empty s2 \<or> mips_mem s1 = mips_mem s2) \<and>
     (wb_empty s1 \<and> wb_empty s2 \<or> mips_wb s1 = mips_wb s2)\<close>

lemma aux:
  assumes \<open>\<not> mips_de_valid (impl_step im s)\<close>
    and \<open>\<not> stall s\<close>
  shows \<open>proj (flush1 (flush1 (flush1 (flush1 s)))) = proj (flush1 (flush1 (flush1 (impl_step im s))))\<close>
proof-
  let ?s1' = \<open>flush1 (flush1 s)\<close>
  let ?s2' = \<open>flush1 (impl_step im s)\<close>
  let ?s1'' = \<open>flush1 (flush1 (flush1 s))\<close>
  let ?s2'' = \<open>flush1 (flush1 (impl_step im s))\<close>
  let ?s1'3 = \<open>flush1 (flush1 (flush1 (flush1 s)))\<close>
  let ?s2'3 = \<open>flush1 (flush1 (flush1 (impl_step im s)))\<close>
  have same_pc1: \<open>mips_pc (flush1 s) = mips_pc (impl_step im s)\<close> using a2[OF assms(1)] .
  have same_rf1: \<open>mips_rf (flush1 s) = mips_rf (impl_step im s)\<close> using a3 .
  have same_dm1: \<open>mips_dm (flush1 s) = mips_dm (impl_step im s)\<close> using a4 .
  from assms(1) de_invalid_to_de_valid have \<open>mips_de_valid s\<close> by blast
  have \<open>\<not> mips_de_valid (flush1 s)\<close> using assms(2) \<open>mips_de_valid s\<close>
    by (simp add: flush1_def mips_upd_def Let_def data_hazard_def eqnz_def stall_def)
  from b1[OF same_pc1 same_rf1 same_dm1 this assms(1)] a1
  have \<open>mips_pc ?s1' = mips_pc ?s2' \<and> mips_rf ?s1' = mips_rf ?s2' \<and> mips_dm ?s1' = mips_dm ?s2' \<and>
        \<not> mips_de_valid ?s1' \<and> \<not> mips_de_valid ?s2' \<and> ex_empty ?s1' \<and> ex_empty ?s2' \<and> mips_mem ?s1' = mips_mem ?s2' \<and> mips_wb ?s1' = mips_wb ?s2'\<close>
    by blast
  with b2
  have \<open>mips_pc ?s1'' = mips_pc ?s2'' \<and> mips_rf ?s1'' = mips_rf ?s2'' \<and> mips_dm ?s1'' = mips_dm ?s2'' \<and>
        \<not> mips_de_valid ?s1'' \<and> \<not> mips_de_valid ?s2'' \<and> ex_empty ?s1'' \<and> ex_empty ?s2'' \<and> mem_empty ?s1'' \<and> mem_empty ?s2'' \<and> mips_wb ?s1'' = mips_wb ?s2''\<close>
    by blast
  with b3
  have \<open>mips_pc ?s1'3 = mips_pc ?s2'3 \<and> mips_rf ?s1'3 = mips_rf ?s2'3 \<and> mips_dm ?s1'3 = mips_dm ?s2'3 \<and>
        \<not> mips_de_valid ?s1'3 \<and> \<not> mips_de_valid ?s2'3 \<and> ex_empty ?s1'3 \<and> ex_empty ?s2'3 \<and> mem_empty ?s1'3 \<and> mem_empty ?s2'3 \<and> wb_empty ?s1'3 \<and> wb_empty ?s2'3\<close>
    by blast
  then show ?thesis by (simp add: proj_def)
qed

lemma exec_correct_kill:
  \<open>s1 = impl_step im s0 \<Longrightarrow> \<not> stall s0 \<Longrightarrow> \<not> mips_de_valid s1 \<Longrightarrow> abstract s0 = abstract s1\<close>
  apply(simp (no_asm) add: impl_step_def abstract_def)
  apply(subst flush_de_empty[of s1])
   apply assumption
  apply(subgoal_tac \<open>mips_de_valid s0\<close>)
   prefer 2 using de_invalid_to_de_valid apply blast
  apply(simp add: flush_def run_until_no_stall_def flush_till_ex_def)
  using aux by blast

lemma ex_and_mem_empty_imp_no_stall':
  \<open>ex_empty s \<Longrightarrow> mem_empty s \<Longrightarrow> run_until_no_stall s = s\<close>
  apply(subgoal_tac \<open>\<not> stall s\<close>)
   apply(simp add: run_until_no_stall_def)
  by (fact ex_and_mem_empty_imp_no_stall)

find_theorems flushed flush1

lemma flushed_imp_abstract_is_proj:
  \<open>flushed s \<Longrightarrow> abstract s = proj s\<close>
  apply(auto simp add: abstract_def flush_def flush_till_ex_def)
  using flush1_flushed flush1_same_proj apply metis
  by (simp add: flushed_def)

lemma flush1_same_pc:
  \<open>\<not> mips_de_valid s \<Longrightarrow> mips_pc (flush1 s) = mips_pc s\<close>
  by (simp add: flush1_def mips_upd_def Let_def next_pc_def)

lemma de_empty_imp_next_de_empty:
  \<open>\<not> mips_de_valid s \<Longrightarrow> \<not> mips_de_valid (flush1 s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

(* lemma one_ALU_R_pc:
  \<open>flushed s \<Longrightarrow> mips_de_valid (impl_step im s) \<Longrightarrow> mips.decode (im (mips_pc s)) = Inst_ALU_R op rd rs rt \<Longrightarrow> mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) = mips_pc s + 1\<close>
  apply(subgoal_tac \<open>mips_pc (impl_step im s) = mips_pc s + 1\<close>)
   prefer 2 apply(simp add: impl_step_def mips_upd_def Let_def flushed_def data_hazard_def eqnz_def)
  apply(clarsimp simp add: flushed_def Let_def)
  apply(subgoal_tac \<open>\<not> mips_de_valid (flush1 (impl_step im s))\<close>)
   prefer 2 apply(simp add: flush1_def mips_upd_def impl_step_def Let_def data_hazard_def eqnz_def)
  apply(subgoal_tac \<open>\<not> mips_de_valid (flush1 (flush1 (impl_step im s)))\<close>)
   prefer 2 using de_empty_imp_next_de_empty apply blast
  apply(subgoal_tac \<open>\<not> mips_de_valid (flush1 (flush1 (flush1 (impl_step im s))))\<close>)
   prefer 2 using de_empty_imp_next_de_empty apply blast
  apply(subgoal_tac \<open>mips_pc (flush1 (impl_step im s)) = mips_pc (impl_step im s)\<close>)
  using flush1_same_pc[of \<open>flush1 (impl_step im s)\<close>] flush1_same_pc[of \<open>flush1 (flush1 (impl_step im s))\<close>] flush1_same_pc[of \<open>flush1 (flush1 (flush1 (impl_step im s)))\<close>] apply simp
  apply(simp add: impl_step_def mips_upd_def Let_def data_hazard_def eqnz_def flush1_def)
  apply(simp add: mips_out_im_addr_def)
  apply(simp add: decode_ALU_R_next_pc_sel)
  done *)

lemma wb_nop:
  \<open>WritebackStage_rf_wa (mips_wb s) = 0 \<Longrightarrow> regfile_r (mips_rf (flush1 s)) = regfile_r (mips_rf s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def)

lemma wb_alu_out:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = ALU_Out \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) = write_rf (WritebackStage_rf_wa (mips_wb s)) (WritebackStage_alu_out (mips_wb s)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def write_rf_def rf_in_def)

lemma wb_shifter_out:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = ShifterOut \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) = write_rf (WritebackStage_rf_wa (mips_wb s)) (WritebackStage_shifter_out (mips_wb s)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def write_rf_def rf_in_def)

lemma wb_pc_plus8:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = PC_plus8 \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) = write_rf (WritebackStage_rf_wa (mips_wb s)) (word_cat (WritebackStage_pc (mips_wb s) + 1) (0::2 word)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def write_rf_def rf_in_def)

lemma wb_lb:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = DM_Out \<Longrightarrow>
   WritebackStage_dm_req_size (mips_wb s) = Byte \<Longrightarrow>
   WritebackStage_mem_data_sign_ext (mips_wb s) \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) =
   write_rf (WritebackStage_rf_wa (mips_wb s)) (scast (ucast (dmem_out_out (mips_dm s)) :: 8 word)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def ucast_slice write_rf_def rf_in_def)

lemma wb_lbu:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = DM_Out \<Longrightarrow>
   WritebackStage_dm_req_size (mips_wb s) = Byte \<Longrightarrow>
   \<not> WritebackStage_mem_data_sign_ext (mips_wb s) \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) =
   write_rf (WritebackStage_rf_wa (mips_wb s)) (ucast (ucast (dmem_out_out (mips_dm s)) :: 8 word)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def ucast_slice write_rf_def rf_in_def)

lemma wb_lh:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = DM_Out \<Longrightarrow>
   WritebackStage_dm_req_size (mips_wb s) = Half \<Longrightarrow>
   WritebackStage_mem_data_sign_ext (mips_wb s) \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) =
   write_rf (WritebackStage_rf_wa (mips_wb s)) (scast (ucast (dmem_out_out (mips_dm s)) :: 16 word)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def ucast_slice write_rf_def rf_in_def)

lemma wb_lhu:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = DM_Out \<Longrightarrow>
   WritebackStage_dm_req_size (mips_wb s) = Half \<Longrightarrow>
   \<not> WritebackStage_mem_data_sign_ext (mips_wb s) \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) =
   write_rf (WritebackStage_rf_wa (mips_wb s)) (ucast (ucast (dmem_out_out (mips_dm s)) :: 16 word)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def ucast_slice write_rf_def rf_in_def)

lemma wb_lw:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = DM_Out \<Longrightarrow>
   WritebackStage_dm_req_size (mips_wb s) = Word \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) =
   write_rf (WritebackStage_rf_wa (mips_wb s)) (dmem_out_out (mips_dm s)) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def write_rf_def rf_in_def)

lemma rf_wa_mem_wb:
  \<open>WritebackStage_rf_wa (mips_wb (flush1 s)) = MemoryStage_rf_wa (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma rf_wa_ex_mem:
  \<open>MemoryStage_rf_wa (mips_mem (flush1 s)) = ExecuteStage_rf_wa (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma rf_wa_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow> ExecuteStage_rf_wa (mips_ex (flush1 s)) = DecodedInst_rf_wa (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def)

lemma rf_wa_de_ex_stall:
  \<open>mips_de_valid s \<Longrightarrow> stall s \<Longrightarrow> ExecuteStage_rf_wa (mips_ex (flush1 s)) = 0\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def)

lemma rf_wa_de_ex_invalid:
  \<open>\<not> mips_de_valid s \<Longrightarrow> ExecuteStage_rf_wa (mips_ex (flush1 s)) = 0\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma rf_in_sel_mem_wb:
  \<open>WritebackStage_rf_in_sel (mips_wb (flush1 s)) = MemoryStage_rf_in_sel (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma rf_in_sel_ex_mem:
  \<open>MemoryStage_rf_in_sel (mips_mem (flush1 s)) = ExecuteStage_rf_in_sel (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma rf_in_sel_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_rf_in_sel (mips_ex (flush1 s)) = DecodedInst_rf_in_sel (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma alu_out_mem_wb:
  \<open>WritebackStage_alu_out (mips_wb (flush1 s)) = MemoryStage_alu_out (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma alu_out_ex_mem_reg:
  \<open>\<not> ExecuteStage_alu_b_imm (mips_ex s) \<Longrightarrow> MemoryStage_alu_out (mips_mem (flush1 s)) = alu (ExecuteStage_r1 (mips_ex s)) (ExecuteStage_r2 (mips_ex s)) (ExecuteStage_alu_op (mips_ex s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma alu_out_ex_mem_imm:
  \<open>ExecuteStage_alu_b_imm (mips_ex s) \<Longrightarrow> MemoryStage_alu_out (mips_mem (flush1 s)) = alu (ExecuteStage_r1 (mips_ex s)) (ExecuteStage_imm32 (mips_ex s)) (ExecuteStage_alu_op (mips_ex s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma shifter_out_mem_wb:
  \<open>WritebackStage_shifter_out (mips_wb (flush1 s)) = MemoryStage_shifter_out (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma shifter_out_ex_mem_reg:
  \<open>\<not> ExecuteStage_shamt_imm (mips_ex s) \<Longrightarrow> MemoryStage_shifter_out (mips_mem (flush1 s)) = shifter (ExecuteStage_r2 (mips_ex s)) (ucast (ExecuteStage_r1 (mips_ex s))) (ExecuteStage_shifter_op (mips_ex s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def ucast_slice)

lemma shifter_out_ex_mem_imm:
  \<open>ExecuteStage_shamt_imm (mips_ex s) \<Longrightarrow> MemoryStage_shifter_out (mips_mem (flush1 s)) = shifter (ExecuteStage_r2 (mips_ex s)) (ExecuteStage_shamt (mips_ex s)) (ExecuteStage_shifter_op (mips_ex s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma alu_op_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_alu_op (mips_ex (flush1 s)) = DecodedInst_alu_op (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma shifter_op_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_shifter_op (mips_ex (flush1 s)) = DecodedInst_shifter_op (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma flushed_imp_impl_step_no_stall:
  \<open>flushed s \<Longrightarrow> \<not> stall (impl_step im s)\<close>
  by (simp add: flushed_def stall_def impl_step_def mips_upd_def Let_def data_hazard_def eqnz_def)

lemma impl_step_inst_conv:
  \<open>\<not> mips_de_valid s \<Longrightarrow> mips_inst (impl_step im s) = im (mips_pc s)\<close>
  by (simp add: impl_step_def mips_upd_def Let_def data_hazard_def eqnz_def mips_out_im_addr_def)

lemma impl_step_inst_conv2:
  \<open>\<not> stall s \<Longrightarrow> mips_inst (impl_step im s) = im (mips_pc s)\<close>
  by (auto simp add: impl_step_def mips_upd_def Let_def stall_def mips_out_im_addr_def)

lemma flush3_same_pc:
  \<open>\<not> mips_de_valid s \<Longrightarrow> mips_pc (flush1 (flush1 (flush1 s))) = mips_pc s\<close>
  using de_empty_imp_next_de_empty flush1_same_pc by simp

lemma ex_empty_imp_next_mem_empty:
  \<open>ex_empty s \<Longrightarrow> mem_empty (flush1 s)\<close>
  by (simp add: Let_def flush1_def mips_upd_def)

lemma ex_empty_imp_next_mem_empty':
  \<open>ex_empty s \<Longrightarrow> mem_empty (impl_step im s)\<close>
  by (simp add: Let_def impl_step_def mips_upd_def)

lemma mem_empty_imp_next_wb_empty:
  \<open>mem_empty s \<Longrightarrow> wb_empty (flush1 s)\<close>
  by (simp add: Let_def flush1_def mips_upd_def)

lemma not_jb_pc_unchanged:
  \<open>not_jb (mips.decode (mips_inst s)) \<Longrightarrow> mips_pc (flush1 s) = mips_pc s\<close>
  apply(drule decode_not_jb_next_pc_sel)
  by (simp add: flush1_def mips_upd_def Let_def next_pc_def)

lemma stall_imp_inst_unchanged:
  \<open>stall s \<Longrightarrow> mips_inst (flush1 s) = mips_inst s\<close>
  by (auto simp add: stall_def flush1_def mips_upd_def Let_def)

lemma read_rf_eq1:
  \<open>regfile_out_out1 ra1 wa d (mips_rf s) =
   read_rf ra1 (regfile_r (regfile_upd wa d (mips_rf s)))\<close>
  by (simp add: regfile_out_out1_def read_rf_def regfile_upd_def Let_def)

lemma read_rf_eq2:
  \<open>regfile_out_out2 ra2 wa d (mips_rf s) =
   read_rf ra2 (regfile_r (regfile_upd wa d (mips_rf s)))\<close>
  by (simp add: regfile_out_out2_def read_rf_def regfile_upd_def Let_def)

lemma J_update_pc:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_J \<Longrightarrow>
   mips_pc (flush1 s) = word_cat (slice 26 (mips_pc s) :: 4 word) (UCAST(32\<rightarrow>26) (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice next_pc_def)

lemma JR_update_pc:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_RS \<Longrightarrow>
   mips_pc (flush1 s) = slice 2 (read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def read_rf_eq1 next_pc_def)

lemma BEQ_update_pc:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondEQ \<Longrightarrow>
   read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) =
   read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s + scast (UCAST(32\<rightarrow>16) (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 read_rf_eq2 next_pc_def)

lemma BNE_update_pc:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondNE \<Longrightarrow>
   read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) \<noteq>
   read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s + scast (UCAST(32\<rightarrow>16) (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 read_rf_eq2 next_pc_def)

lemma BLEZ_update_pc:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondLEZ \<Longrightarrow>
   sint (read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))) \<le> 0 \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s + scast (UCAST(32\<rightarrow>16) (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 next_pc_def)

lemma BGTZ_update_pc:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondGTZ \<Longrightarrow>
   sint (read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))) > 0 \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s + scast (UCAST(32\<rightarrow>16) (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 next_pc_def)

lemma BEQ_update_pc_nt:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondEQ \<Longrightarrow>
   read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) \<noteq>
   read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 read_rf_eq2 next_pc_def)

lemma BNE_update_pc_nt:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondNE \<Longrightarrow>
   read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) =
   read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s))) \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 read_rf_eq2 next_pc_def)

lemma BLEZ_update_pc_nt:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondLEZ \<Longrightarrow>
   sint (read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))) > 0 \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 next_pc_def)

lemma BGTZ_update_pc_nt:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow>
   DecodedInst_next_pc_sel (decode (mips_inst s)) = NextPC_B \<Longrightarrow>
   DecodedInst_cond_sel (decode (mips_inst s)) = CondGTZ \<Longrightarrow>
   sint (read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))) \<le> 0 \<Longrightarrow>
   mips_pc (flush1 s) = mips_pc s\<close>
  by (simp add: flush1_def mips_upd_def Let_def stall_def ucast_slice read_rf_eq1 next_pc_def)

lemma inst_conv:
  \<open>\<not> stall s \<Longrightarrow> mips_inst (impl_step im s) = im (mips_pc s)\<close>
  by (auto simp add: stall_def impl_step_def mips_upd_def Let_def mips_out_im_addr_def)

lemma stall_pc_unchanged:
  \<open>stall s \<Longrightarrow> mips_pc (flush1 s) = mips_pc s\<close>
  by (auto simp add: stall_def flush1_def mips_upd_def Let_def)

lemma impl_step_inc_pc:
  \<open>\<not> stall s \<Longrightarrow> mips_de_valid (impl_step im s) \<Longrightarrow> mips_pc (impl_step im s) = mips_pc s + 1\<close>
  by (auto simp add: stall_def impl_step_def mips_upd_def Let_def next_pc_def)

lemma flush1_same_pc2:
  \<open>mips_de_valid (impl_step im s) \<Longrightarrow> mips_pc (flush1 s) = mips_pc s\<close>
  by (simp add: impl_step_def flush1_def mips_upd_def Let_def next_pc_def)

lemma stall_imp_next_de_valid:
  \<open>stall s \<Longrightarrow> mips_de_valid (flush1 s)\<close>
  apply(cases \<open>mips_de_valid s\<close>)
   apply(simp add: stall_def flush1_def mips_upd_def Let_def)
  using de_empty_imp_no_stall by blast

lemma stall_imp_next_de_valid':
  \<open>stall s \<Longrightarrow> mips_de_valid (impl_step im s)\<close>
  apply(cases \<open>mips_de_valid s\<close>)
   apply(simp add: stall_def impl_step_def mips_upd_def Let_def)
  using de_empty_imp_no_stall by blast

lemma alu_b_imm_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_alu_b_imm (mips_ex (flush1 s)) = DecodedInst_alu_b_imm (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma shamt_imm_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_shamt_imm (mips_ex (flush1 s)) = DecodedInst_shamt_imm (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma r1_de_ex_nowrite:
  \<open>mips_de_valid s \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) = 0 \<Longrightarrow> ExecuteStage_r1 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out1_def read_rf_def)

lemma r1_de_ex_write_other:
  \<open>mips_de_valid s \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) \<noteq> 0 \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) \<noteq> DecodedInst_rf_ra1 (decode (mips_inst s)) \<Longrightarrow>
   ExecuteStage_r1 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out1_def read_rf_def)

(*
lemma r1_de_ex_forward:
  \<open>mips_de_valid s \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) \<noteq> 0 \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) = DecodedInst_rf_ra1 (decode (mips_inst s)) \<Longrightarrow>
   ExecuteStage_r1 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out1_def read_rf_def regfile_upd_def)
*)

lemma r2_de_ex_nowrite:
  \<open>mips_de_valid s \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) = 0 \<Longrightarrow> ExecuteStage_r2 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out2_def read_rf_def)

lemma r2_de_ex_write_other:
  \<open>mips_de_valid s \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) \<noteq> 0 \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) \<noteq> DecodedInst_rf_ra2 (decode (mips_inst s)) \<Longrightarrow>
   ExecuteStage_r2 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out2_def read_rf_def)

(*
lemma r2_de_ex_forward:
  \<open>mips_de_valid s \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) \<noteq> 0 \<Longrightarrow> WritebackStage_rf_wa (mips_wb s) = DecodedInst_rf_ra2 (decode (mips_inst s)) \<Longrightarrow>
   ExecuteStage_r2 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out2_def read_rf_def regfile_upd_def)
*)

lemma r1_de_ex':
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_r1 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra1 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out1_def read_rf_def regfile_upd_def)

lemma r2_de_ex':
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_r2 (mips_ex (flush1 s)) = read_rf (DecodedInst_rf_ra2 (decode (mips_inst s))) (regfile_r (mips_rf (flush1 s)))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_out_out2_def read_rf_def regfile_upd_def)

lemma same_regfile:
  \<open>regfile_r (mips_rf s) = regfile_r (mips_rf t) \<Longrightarrow> mips_wb s = mips_wb t \<Longrightarrow> dmem_out_out (mips_dm s) = dmem_out_out (mips_dm t) \<Longrightarrow> regfile_r (mips_rf (flush1 s)) = regfile_r (mips_rf (flush1 t))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def)

lemma same_dmem:
  \<open>dmem_m (mips_dm s) = dmem_m (mips_dm t) \<Longrightarrow> mips_mem s = mips_mem t \<Longrightarrow> dmem_m (mips_dm (flush1 s)) = dmem_m (mips_dm (flush1 t))\<close>
  apply(simp add: flush1_def mips_upd_def Let_def dmem_upd_def)
  apply(cases \<open>MemoryStage_dm_req_size (mips_mem t)\<close>; simp)
  done

lemma flush1_step:
  \<open>mips_rf (flush1 s) = mips_rf (impl_step im s) \<and>
   mips_dm (flush1 s) = mips_dm (impl_step im s) \<and>
   mips_ex (flush1 s) = mips_ex (impl_step im s) \<and>
   mips_mem (flush1 s) = mips_mem (impl_step im s) \<and>
   mips_wb (flush1 s) = mips_wb (impl_step im s)\<close>
  by (simp add: flush1_def impl_step_def mips_upd_def Let_def)

lemma flush1_step_1:
  \<open>mips_rf s = mips_rf t \<and>
   mips_dm s = mips_dm t \<and>
   mips_ex s = mips_ex t \<and>
   mips_mem s = mips_mem t \<and>
   mips_wb s = mips_wb t \<Longrightarrow>
   mips_rf (flush1 s) = mips_rf (flush1 t) \<and>
   mips_dm (flush1 s) = mips_dm (flush1 t) \<and>
   mips_mem (flush1 s) = mips_mem (flush1 t) \<and>
   mips_wb (flush1 s) = mips_wb (flush1 t)\<close>
  by (simp add: flush1_def impl_step_def mips_upd_def Let_def)

lemma flush1_step_2:
  \<open>mips_rf s = mips_rf t \<and>
   mips_dm s = mips_dm t \<and>
   mips_mem s = mips_mem t \<and>
   mips_wb s = mips_wb t \<Longrightarrow>
   mips_rf (flush1 s) = mips_rf (flush1 t) \<and>
   mips_dm (flush1 s) = mips_dm (flush1 t) \<and>
   mips_wb (flush1 s) = mips_wb (flush1 t)\<close>
  by (simp add: flush1_def impl_step_def mips_upd_def Let_def)

lemma regfile_conv_4_3':
  \<open>regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s0))))) = regfile_r (mips_rf (flush1 (flush1 (flush1 (impl_step im s0)))))\<close>
  apply(subgoal_tac \<open>mips_rf (flush1 (flush1 s0)) = mips_rf (flush1 (impl_step im s0)) \<and>
   mips_dm (flush1 (flush1 s0)) = mips_dm (flush1 (impl_step im s0)) \<and>
   mips_mem (flush1 (flush1 s0)) = mips_mem (flush1 (impl_step im s0)) \<and>
   mips_wb (flush1 (flush1 s0)) = mips_wb (flush1 (impl_step im s0))\<close>)
   prefer 2 apply(rule flush1_step_1) apply(rule flush1_step)
  apply(subgoal_tac \<open>mips_rf (flush1 (flush1 (flush1 s0))) = mips_rf (flush1 (flush1 (impl_step im s0))) \<and>
   mips_dm (flush1 (flush1 (flush1 s0))) = mips_dm (flush1 (flush1 (impl_step im s0))) \<and>
   mips_wb (flush1 (flush1 (flush1 s0))) = mips_wb (flush1 (flush1 (impl_step im s0)))\<close>)
   prefer 2 apply(erule flush1_step_2)
  apply(rule same_regfile)
    apply argo+
  done

lemma dmem_unchanged:
  \<open>\<not> MemoryStage_dm_en (mips_mem s) \<or> \<not> MemoryStage_dm_wr (mips_mem s) \<Longrightarrow>
   dmem_m (mips_dm (flush1 s)) = dmem_m (mips_dm s)\<close>
  by (auto simp add: flush1_def mips_upd_def Let_def dmem_upd_def)

lemma dmem_conv_3_2':
  \<open>dmem_m (mips_dm (flush1 (flush1 (flush1 s0)))) = dmem_m (mips_dm (flush1 (flush1 (impl_step im s0))))\<close>
  apply(subgoal_tac \<open>mips_rf (flush1 (flush1 s0)) = mips_rf (flush1 (impl_step im s0)) \<and>
   mips_dm (flush1 (flush1 s0)) = mips_dm (flush1 (impl_step im s0)) \<and>
   mips_mem (flush1 (flush1 s0)) = mips_mem (flush1 (impl_step im s0)) \<and>
   mips_wb (flush1 (flush1 s0)) = mips_wb (flush1 (impl_step im s0))\<close>)
   prefer 2 apply(rule flush1_step_1) apply(rule flush1_step)
  apply(subgoal_tac \<open>mips_rf (flush1 (flush1 (flush1 s0))) = mips_rf (flush1 (flush1 (impl_step im s0))) \<and>
   mips_dm (flush1 (flush1 (flush1 s0))) = mips_dm (flush1 (flush1 (impl_step im s0))) \<and>
   mips_wb (flush1 (flush1 (flush1 s0))) = mips_wb (flush1 (flush1 (impl_step im s0)))\<close>)
   prefer 2 apply(erule flush1_step_2)
  apply(rule same_dmem)
   apply argo+
  done

lemma dm_en_ex_mem:
  \<open>MemoryStage_dm_en (mips_mem (flush1 s)) = ExecuteStage_dm_en (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma dm_en_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow> ExecuteStage_dm_en (mips_ex (flush1 s)) = DecodedInst_dm_en (decode (mips_inst s))\<close>
  by (simp add: stall_def flush1_def mips_upd_def Let_def)

lemma run_until_no_stall_same:
  \<open>\<not> stall s \<Longrightarrow> run_until_no_stall s = s\<close>
  by (simp add: stall_def run_until_no_stall_def)

lemma alu_correct:
  \<open>alu a b (convert_alu_op op) = ALU_op_fn op a b\<close>
  apply(simp add: alu_def)
  apply(cases op; simp)
  by (simp add: word_sless_alt)

lemma shifter_correct:
  \<open>shifter a b (convert_shift_op op) = shift_op_fn op a b\<close>
  apply(simp add: shifter_def)
  by (cases op; simp)

lemma imm32_de_ex_sign_ext:
  \<open>mips_de_valid s \<Longrightarrow> DecodedInst_imm_ext_method (decode (mips_inst s)) = SignExt \<Longrightarrow> ExecuteStage_imm32 (mips_ex (flush1 s)) = scast (ucast (mips_inst s) :: 16 word)\<close>
  by (simp add: flush1_def mips_upd_def Let_def ucast_slice)

lemma imm32_de_ex_zero_ext:
  \<open>mips_de_valid s \<Longrightarrow> DecodedInst_imm_ext_method (decode (mips_inst s)) = ZeroExt \<Longrightarrow> ExecuteStage_imm32 (mips_ex (flush1 s)) = ucast (ucast (mips_inst s) :: 16 word)\<close>
  by (simp add: flush1_def mips_upd_def Let_def ucast_slice)

lemma imm32_de_ex_lui_ext:
  \<open>mips_de_valid s \<Longrightarrow> DecodedInst_imm_ext_method (decode (mips_inst s)) = LUI_Ext \<Longrightarrow> ExecuteStage_imm32 (mips_ex (flush1 s)) = word_cat (UCAST(32\<rightarrow>16) (mips_inst s)) (0::16 word)\<close>
  apply (simp add: flush1_def mips_upd_def Let_def)
  by word_bitwise

lemma de_no_read_imp_no_stall:
  \<open>mips_de_valid s \<Longrightarrow>
   DecodedInst_rf_ra1 (decode (mips_inst s)) = 0 \<Longrightarrow>
   DecodedInst_rf_ra2 (decode (mips_inst s)) = 0 \<Longrightarrow>
   \<not> stall s\<close>
  by (simp add: stall_def data_hazard_def eqnz_def)

lemma shamt_de_ex:
  \<open>ExecuteStage_shamt (mips_ex (flush1 s)) = slice 6 (mips_inst s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma pc_mem_wb:
  \<open>WritebackStage_pc (mips_wb (flush1 s)) = MemoryStage_pc (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma pc_ex_mem:
  \<open>MemoryStage_pc (mips_mem (flush1 s)) = ExecuteStage_pc (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma pc_de_ex:
  \<open>ExecuteStage_pc (mips_ex (flush1 s)) = mips_pc s\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma pc_de_wb:
  \<open>WritebackStage_pc (mips_wb (flush1 (flush1 (flush1 s)))) = mips_pc s\<close>
  using pc_de_ex pc_ex_mem pc_mem_wb by simp

lemma abstract_eq:
  \<open>\<not> stall s \<Longrightarrow> proj (flush s) = proj (flush1 (flush1 (flush1 (flush1 s))))\<close>
  apply(auto simp add: flush_def flush_till_ex_def)
   apply(subgoal_tac \<open>flushed (flush1 (flush1 (flush1 s)))\<close>)
  using flush1_same_proj apply blast
   apply(fold flush_till_ex_def)
   apply(erule flush_till_ex_correct)
  apply(subst run_until_no_stall_same) apply assumption
  apply(rule refl)
  done

lemma next_rf:
  \<open>regfile_r (mips_rf (flush1 s)) = write_rf (WritebackStage_rf_wa (mips_wb s)) (rf_in (mips_wb s) (dmem_out_out (mips_dm s))) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def regfile_upd_def write_rf_def)

lemma rs_conv:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow> rs = DecodedInst_rf_ra1 (decode (mips_inst s)) \<Longrightarrow>
   (read_rf rs (regfile_r (mips_rf (flush1 s)))) =
   (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 s))))))\<close>
  apply(subst next_rf[of \<open>flush1 (flush1 s)\<close>])
  apply(subst next_rf[of \<open>flush1 s\<close>])
  apply(subst rf_wa_mem_wb)
  apply(subst rf_wa_ex_mem)
  apply(subst rf_wa_mem_wb)
  by (simp add: write_rf_def read_rf_def stall_def Let_def data_hazard_def eqnz_def)

lemma rt_conv:
  \<open>mips_de_valid s \<Longrightarrow> \<not> stall s \<Longrightarrow> rs = DecodedInst_rf_ra2 (decode (mips_inst s)) \<Longrightarrow>
   (read_rf rs (regfile_r (mips_rf (flush1 s)))) =
   (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 s))))))\<close>
  apply(subst next_rf[of \<open>flush1 (flush1 s)\<close>])
  apply(subst next_rf[of \<open>flush1 s\<close>])
  apply(subst rf_wa_mem_wb)
  apply(subst rf_wa_ex_mem)
  apply(subst rf_wa_mem_wb)
  by (simp add: write_rf_def read_rf_def stall_def Let_def data_hazard_def eqnz_def)

lemma dm_req_size_mem_wb:
  \<open>WritebackStage_dm_req_size (mips_wb (flush1 s)) = MemoryStage_dm_req_size (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma dm_req_size_ex_mem:
  \<open>MemoryStage_dm_req_size (mips_mem (flush1 s)) = ExecuteStage_dm_req_size (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma dm_req_size_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_dm_req_size (mips_ex (flush1 s)) = DecodedInst_dm_req_size (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma mem_data_sign_ext_mem_wb:
  \<open>WritebackStage_mem_data_sign_ext (mips_wb (flush1 s)) = MemoryStage_mem_data_sign_ext (mips_mem s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma mem_data_sign_ext_ex_mem:
  \<open>MemoryStage_mem_data_sign_ext (mips_mem (flush1 s)) = ExecuteStage_mem_data_sign_ext (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma mem_data_sign_ext_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_mem_data_sign_ext (mips_ex (flush1 s)) = DecodedInst_mem_data_sign_ext (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma dm_out_mem_wb_lb:
  \<open>MemoryStage_dm_en (mips_mem s) \<Longrightarrow> \<not> MemoryStage_dm_wr (mips_mem s) \<Longrightarrow>
   MemoryStage_dm_req_size (mips_mem s) = Byte \<Longrightarrow>
   dmem_out_out (mips_dm (flush1 s)) = ucast (dmem_m (mips_dm s) (ucast (MemoryStage_alu_out (mips_mem s))))\<close>
  apply (simp add: flush1_def mips_upd_def Let_def dmem_out_out_def dmem_upd_def ucast_slice)
  by word_bitwise

lemma dm_out_mem_wb_lh:
  \<open>MemoryStage_dm_en (mips_mem s) \<Longrightarrow> \<not> MemoryStage_dm_wr (mips_mem s) \<Longrightarrow>
   MemoryStage_dm_req_size (mips_mem s) = Half \<Longrightarrow>
   dmem_out_out (mips_dm (flush1 s)) =
   UCAST(16\<rightarrow>32)
     (word_cat (dmem_m (mips_dm s) (word_cat (slice 1 (MemoryStage_alu_out (mips_mem s)) :: 11 word) (1::1 word)))
               (dmem_m (mips_dm s) (word_cat (slice 1 (MemoryStage_alu_out (mips_mem s)) :: 11 word) (0::1 word))))\<close>
  apply (simp add: flush1_def mips_upd_def Let_def dmem_out_out_def dmem_upd_def ucast_slice)
  by word_bitwise

lemma dm_wr_ex_mem:
  \<open>MemoryStage_dm_wr (mips_mem (flush1 s)) = ExecuteStage_dm_wr (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma dm_wr_de_ex:
  \<open>mips_de_valid s \<Longrightarrow> ExecuteStage_dm_wr (mips_ex (flush1 s)) = DecodedInst_dm_wr (decode (mips_inst s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma dm_unchanged:
  \<open>mem_empty s \<Longrightarrow> mips_dm (flush1 s) = mips_dm s\<close>
  by (simp add: flush1_def mips_upd_def Let_def dmem_upd_def)

lemma store_update_dm:
  \<open>MemoryStage_dm_en (mips_mem s) \<Longrightarrow> MemoryStage_dm_wr (mips_mem s) \<Longrightarrow>
   dmem_m (mips_dm (flush1 s)) =
   store
     (MemoryStage_alu_out (mips_mem s))
     (case MemoryStage_dm_req_size (mips_mem s) of
        Byte \<Rightarrow> BYTE | Half \<Rightarrow> HALF | Word \<Rightarrow> WORD)
     (MemoryStage_dm_in (mips_mem s))
     (dmem_m (mips_dm s))\<close>
  apply(simp add: flush1_def mips_upd_def Let_def dmem_upd_def store_def)
  by (cases \<open>MemoryStage_dm_req_size (mips_mem s)\<close>; simp add: ucast_slice Let_def)

lemma dm_out_mem_wb_lw:
  \<open>MemoryStage_dm_en (mips_mem s) \<Longrightarrow> \<not> MemoryStage_dm_wr (mips_mem s) \<Longrightarrow>
   MemoryStage_dm_req_size (mips_mem s) = Word \<Longrightarrow>
   dmem_out_out (mips_dm (flush1 s)) =
   word_cat (dmem_m (mips_dm s) (word_cat (slice 2 (MemoryStage_alu_out (mips_mem s))::10 word) (3::2 word)))
     (word_cat (dmem_m (mips_dm s) (word_cat (slice 2 (MemoryStage_alu_out (mips_mem s))::10 word) (2::2 word)))
       (word_cat (dmem_m (mips_dm s) (word_cat (slice 2 (MemoryStage_alu_out (mips_mem s))::10 word) (1::2 word)))
         (dmem_m (mips_dm s) (word_cat (slice 2 (MemoryStage_alu_out (mips_mem s))::10 word) (0::2 word)))::16 word)::24 word)\<close>
  by (simp add: flush1_def mips_upd_def Let_def dmem_out_out_def dmem_upd_def ucast_slice)

(*
definition rf_din_dm_out where
  "rf_din_dm_out s \<equiv>
     case WritebackStage_dm_req_size (mips_wb s) of
            Byte \<Rightarrow> if WritebackStage_mem_data_sign_ext (mips_wb s) then SCAST(8 \<rightarrow> 32) (slice 0 (dmem_out_out (mips_dm s))) else UCAST(8 \<rightarrow> 32) (slice 0 (dmem_out_out (mips_dm s)))
            | Half \<Rightarrow> if WritebackStage_mem_data_sign_ext (mips_wb s) then SCAST(16 \<rightarrow> 32) (slice 0 (dmem_out_out (mips_dm s))) else UCAST(16 \<rightarrow> 32) (slice 0 (dmem_out_out (mips_dm s)))
            | Word \<Rightarrow> dmem_out_out (mips_dm s)"

lemma wb_dm_out:
  \<open>WritebackStage_rf_in_sel (mips_wb s) = DM_Out \<Longrightarrow>
   regfile_r (mips_rf (flush1 s)) = write_rf (WritebackStage_rf_wa (mips_wb s)) (rf_din_dm_out s) (regfile_r (mips_rf s))\<close>
  by (simp add: flush1_def mips_upd_def Let_def write_rf_def rf_din_dm_out_def regfile_upd_def)
*)

fun is_store where
  \<open>is_store (Inst_Store _ _ _ _) = True\<close> | \<open>is_store _ = False\<close>

lemma not_store_imp_no_dm_write:
  \<open>mips.decode inst \<noteq> Inst_Undef \<Longrightarrow>
   \<not> is_store (mips.decode inst) \<Longrightarrow>
   \<not> DecodedInst_dm_en (decode inst) \<or>
   \<not> DecodedInst_dm_wr (decode inst)\<close>
  apply(cases \<open>mips.decode inst\<close>; simp add: decode_not_ls_dm_en)
  apply(simp add: decode_load_dm_wr)
  done

lemma dm_in_ex_mem:
  \<open>MemoryStage_dm_in (mips_mem (flush1 s)) = ExecuteStage_r2 (mips_ex s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma exec_correct:
  assumes s_no_stall: \<open>\<not> stall s\<close>
    and s'_de_valid: \<open>mips_de_valid (impl_step im s)\<close>
    and s'_no_stall: \<open>\<not> stall (impl_step im s)\<close>
  shows \<open>mips.exec load store im (abstract s) (abstract (impl_step im s))\<close>
proof(simp add: mips.exec_def abstract_def)
  let ?s1 = \<open>flush1 s\<close>
  let ?s2 = \<open>flush1 ?s1\<close>
  let ?s3 = \<open>flush1 ?s2\<close>
  let ?s4 = \<open>flush1 ?s3\<close>
  let ?s' = \<open>impl_step im s\<close>
  let ?s'1 = \<open>flush1 ?s'\<close>
  let ?s'2 = \<open>flush1 ?s'1\<close>
  let ?s'3 = \<open>flush1 ?s'2\<close>
  let ?s'4 = \<open>flush1 ?s'3\<close>
  have s1_de_empty: \<open>\<not> mips_de_valid ?s1\<close> using no_stall_imp_next_de_empty[OF s_no_stall] .
  have s2_ex_empty: \<open>ex_empty ?s2\<close> using de_empty_imp_next_ex_empty[OF s1_de_empty] .
  have s3_mem_empty: \<open>mem_empty ?s3\<close> using ex_empty_imp_next_mem_empty[OF s2_ex_empty] .
      (*have s2_de_empty: \<open>\<not> mips_de_valid ?s2\<close> using de_empty_imp_next_de_empty[OF s1_de_empty] .
  have s3_de_empty: \<open>\<not> mips_de_valid ?s3\<close> using de_empty_imp_next_de_empty[OF s2_de_empty] .*)
  have s'1_de_empty: \<open>\<not> mips_de_valid ?s'1\<close> using no_stall_imp_next_de_empty[OF s'_no_stall] .
  have s'2_ex_empty: \<open>ex_empty ?s'2\<close> using de_empty_imp_next_ex_empty[OF s'1_de_empty] .
  have s'3_mem_empty: \<open>mem_empty ?s'3\<close> using ex_empty_imp_next_mem_empty[OF s'2_ex_empty] .
  have s'2_de_empty: \<open>\<not> mips_de_valid ?s'2\<close> using de_empty_imp_next_de_empty[OF s'1_de_empty] .
  have s'3_de_empty: \<open>\<not> mips_de_valid ?s'3\<close> using de_empty_imp_next_de_empty[OF s'2_de_empty] .
  have s'_inst_conv: \<open>mips_inst ?s' = im (mips_pc s)\<close> using inst_conv[OF s_no_stall] .
  have s4_pc_conv: \<open>mips_pc (flush1 (flush1 (flush1 (flush1 s)))) = mips_pc s\<close>
    apply(subst flush3_same_pc[OF s1_de_empty])
    apply(rule flush1_same_pc2[OF s'_de_valid])
    done
  note rf_conv_4_3' = regfile_conv_4_3'[of s im]

  have not_jb_pc_correct: \<open>not_jb (mips.decode (im (mips_pc s))) \<Longrightarrow> mips_pc ?s'4 = mips_pc ?s4 + 1\<close>
    apply(subst flush1_same_pc[OF s'3_de_empty])
    apply(subst flush1_same_pc[OF s'2_de_empty])
    apply(subst flush1_same_pc[OF s'1_de_empty])
    apply(subst not_jb_pc_unchanged) apply(subst s'_inst_conv) apply assumption
    apply(subst s4_pc_conv)
    by (rule impl_step_inc_pc[OF s_no_stall s'_de_valid])

  have not_store_dm_correct:
    \<open>mips.decode (im (mips_pc s)) \<noteq> Inst_Undef \<Longrightarrow>
     \<not> is_store (mips.decode (im (mips_pc s))) \<Longrightarrow>
     dmem_m (mips_dm ?s'4) = dmem_m (mips_dm ?s4)\<close>
    apply(subst dmem_unchanged[of ?s'3])
    using s'3_mem_empty apply(simp add: Let_def)
    apply(subst dmem_unchanged[of ?s'2])
     apply(subst dm_en_ex_mem)
     apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
     apply(subst s'_inst_conv)
     apply(subst dm_wr_ex_mem)
     apply(subst dm_wr_de_ex[OF s'_de_valid])
     apply(subst s'_inst_conv)
    using not_store_imp_no_dm_write apply blast
    apply(subst dmem_unchanged[of ?s3])
    using s3_mem_empty apply(simp add: Let_def)
    by (rule dmem_conv_3_2'[symmetric])

  have no_write_rf_correct:
    "mips.decode (im (mips_pc s)) \<noteq> Inst_Undef \<Longrightarrow>
     write_r (mips.decode (im (mips_pc s))) = 0 \<Longrightarrow>
     regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
     regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))"
  proof-
    assume not_undef: "mips.decode (im (mips_pc s)) \<noteq> Inst_Undef"
    assume no_write: "write_r (mips.decode (im (mips_pc s))) = 0"
    show ?thesis
      apply(subst wb_nop)
       apply(subst rf_wa_mem_wb)
       apply(subst rf_wa_ex_mem)
       apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
       apply(subst s'_inst_conv)
       apply(simp add: decode_rf_wa[OF not_undef] no_write)
      by (simp add: rf_conv_4_3')
  qed

  have \<open>mips.isa_step load store (proj ?s4) (mips.decode (im (mips_pc s))) (proj ?s'4)\<close>
  proof(cases \<open>mips.decode (im (mips_pc s))\<close>)
    case (Inst_ALU_R op rd rs rt)
    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf rd
     (ALU_op_fn op (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))
       (read_rf rt (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))))
     (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst wb_alu_out)
       apply(subst rf_in_sel_mem_wb)
       apply(subst rf_in_sel_ex_mem)
       apply(subst rf_in_sel_de_ex[OF s'_de_valid])
       apply(simp add: decode_alu_rf_in_sel s'_inst_conv Inst_ALU_R)

      apply(subst rf_wa_mem_wb)
      apply(subst rf_wa_ex_mem)
      apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
      apply(simp add: decode_rf_wa s'_inst_conv Inst_ALU_R)

      apply(subst alu_out_mem_wb)
      apply(subst alu_out_ex_mem_reg)
       apply(subst alu_b_imm_de_ex[OF s'_de_valid])
       apply(simp add: decode_ALU_R_alu_b_imm[OF Inst_ALU_R] s'_inst_conv)

      apply(subst r1_de_ex'[OF s'_de_valid])
      apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply (rule refl)
      apply(simp add: decode_rf_ra1 Inst_ALU_R s'_inst_conv)

      apply(subst r2_de_ex'[OF s'_de_valid])
      apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply (rule refl)
      apply(simp add: decode_rf_ra2 Inst_ALU_R s'_inst_conv)

      apply(subst alu_op_de_ex[OF s'_de_valid])
      apply(simp add: decode_alu_op Inst_ALU_R s'_inst_conv)

      apply(subst alu_correct)
      by (simp add: rf_conv_4_3')

    from Inst_ALU_R show ?thesis
      apply simp
      apply(rule mips.ALU_R)
      apply(simp add: proj_def)
      using not_jb_pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_ALU_I op rd rs imm)
    have rf_correct_bitwise:
      "is_bitwise_op op \<Longrightarrow>
 regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
     write_rf rd
      (ALU_op_fn op (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))
        (UCAST(16 \<rightarrow> 32) imm))
      (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
    proof-
      assume bitwise: "is_bitwise_op op"
      show ?thesis
        apply(subst wb_alu_out)
         apply(subst rf_in_sel_mem_wb)
         apply(subst rf_in_sel_ex_mem)
         apply(subst rf_in_sel_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_rf_in_sel s'_inst_conv Inst_ALU_I)

        apply(subst rf_wa_mem_wb)
        apply(subst rf_wa_ex_mem)
        apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
        apply(simp add: decode_rf_wa s'_inst_conv Inst_ALU_I)

        apply(subst alu_out_mem_wb)
        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm  Inst_ALU_I s'_inst_conv)

        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply (rule refl)
        apply(simp add: decode_rf_ra1 Inst_ALU_I s'_inst_conv)

        apply(subst imm32_de_ex_zero_ext[OF s'_de_valid])
         apply(simp add: decode_ALU_I_bitwise_imm_ext_method[OF Inst_ALU_I bitwise] s'_inst_conv)
        apply(simp add: decode_imm16 Inst_ALU_I s'_inst_conv)

        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_ALU_I s'_inst_conv)

        apply(subst alu_correct)
        by (simp add: rf_conv_4_3')
    qed

    have rf_correct_non_bitwise:
      "\<not> is_bitwise_op op \<Longrightarrow>
 regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
     write_rf rd
      (ALU_op_fn op (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))
        (SCAST(16 \<rightarrow> 32) imm))
      (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
    proof-
      assume bitwise: "\<not> is_bitwise_op op"
      show ?thesis
        apply(subst wb_alu_out)
         apply(subst rf_in_sel_mem_wb)
         apply(subst rf_in_sel_ex_mem)
         apply(subst rf_in_sel_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_rf_in_sel s'_inst_conv Inst_ALU_I)

        apply(subst rf_wa_mem_wb)
        apply(subst rf_wa_ex_mem)
        apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
        apply(simp add: decode_rf_wa s'_inst_conv Inst_ALU_I)

        apply(subst alu_out_mem_wb)
        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_ALU_I s'_inst_conv)

        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply (rule refl)
        apply(simp add: decode_rf_ra1 Inst_ALU_I s'_inst_conv)

        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ALU_I_non_bitwise_imm_ext_method[OF Inst_ALU_I bitwise] s'_inst_conv)
        apply(simp add: decode_imm16 Inst_ALU_I s'_inst_conv)

        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_ALU_I s'_inst_conv)

        apply(subst alu_correct)
        by (simp add: rf_conv_4_3')
    qed

    from Inst_ALU_I show ?thesis
      apply simp
      apply(rule mips.ALU_I)
      apply(simp add: proj_def)
      using not_jb_pc_correct rf_correct_bitwise rf_correct_non_bitwise not_store_dm_correct by simp
  next
    case (Inst_Shift_R op rd rt rs)
    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf rd
     (shift_op_fn op (read_rf rt (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))
       (UCAST(32 \<rightarrow> 5) (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))))
     (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst wb_shifter_out)
       apply(subst rf_in_sel_mem_wb)
       apply(subst rf_in_sel_ex_mem)
       apply(subst rf_in_sel_de_ex[OF s'_de_valid])
       apply(simp add: decode_shifter_rf_in_sel Inst_Shift_R s'_inst_conv)

      apply(subst rf_wa_mem_wb)
      apply(subst rf_wa_ex_mem)
      apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
      apply(simp add: decode_rf_wa Inst_Shift_R s'_inst_conv)

      apply(subst shifter_out_mem_wb)
      apply(subst shifter_out_ex_mem_reg)
       apply(subst shamt_imm_de_ex[OF s'_de_valid])
       apply(simp add: decode_Shift_R_shamt_imm[OF Inst_Shift_R] s'_inst_conv)

      apply(subst r1_de_ex'[OF s'_de_valid])
      apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
      apply(simp add: decode_rf_ra1 Inst_Shift_R s'_inst_conv)

      apply(subst r2_de_ex'[OF s'_de_valid])
      apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
      apply(simp add: decode_rf_ra2 Inst_Shift_R s'_inst_conv)

      apply(subst shifter_op_de_ex[OF s'_de_valid])
      apply(simp add: decode_shifter_op Inst_Shift_R s'_inst_conv)

      apply(subst shifter_correct)
      by (simp add: rf_conv_4_3')

    from Inst_Shift_R show ?thesis
      apply simp
      apply(rule mips.Shift_R)
      apply(simp add: proj_def)
      using not_jb_pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_Shift_I op rd rt shamt)
    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf rd
     (shift_op_fn op (read_rf rt (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))
       shamt)
     (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst wb_shifter_out)
       apply(subst rf_in_sel_mem_wb)
       apply(subst rf_in_sel_ex_mem)
       apply(subst rf_in_sel_de_ex[OF s'_de_valid])
       apply(simp add: decode_shifter_rf_in_sel Inst_Shift_I s'_inst_conv)

      apply(subst rf_wa_mem_wb)
      apply(subst rf_wa_ex_mem)
      apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
      apply(simp add: decode_rf_wa Inst_Shift_I s'_inst_conv)

      apply(subst shifter_out_mem_wb)
      apply(subst shifter_out_ex_mem_imm)
       apply(subst shamt_imm_de_ex[OF s'_de_valid])
       apply(simp add: decode_Shift_I_shamt_imm[OF Inst_Shift_I] s'_inst_conv)

      apply(subst shamt_de_ex)
      apply(simp add: decode_Shift_I_shamt[OF Inst_Shift_I] s'_inst_conv)

      apply(subst r2_de_ex'[OF s'_de_valid])
      apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
      apply(simp add: decode_rf_ra2 Inst_Shift_I s'_inst_conv)

      apply(subst shifter_op_de_ex[OF s'_de_valid])
      apply(simp add: decode_shifter_op Inst_Shift_I s'_inst_conv)

      apply(subst shifter_correct)
      by (simp add: rf_conv_4_3')

    from Inst_Shift_I show ?thesis
      apply simp
      apply(rule mips.Shift_I)
      apply(simp add: proj_def)
      using not_jb_pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_LUI rd imm)
    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf rd (word_cat imm (0::16 word)) (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst wb_alu_out)
       apply(subst rf_in_sel_mem_wb)
       apply(subst rf_in_sel_ex_mem)
       apply(subst rf_in_sel_de_ex[OF s'_de_valid])
       apply(simp add: decode_alu_rf_in_sel s'_inst_conv Inst_LUI)

      apply(subst rf_wa_mem_wb)
      apply(subst rf_wa_ex_mem)
      apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
      apply(simp add: decode_rf_wa Inst_LUI s'_inst_conv)

      apply(subst alu_out_mem_wb)
      apply(subst alu_out_ex_mem_imm)
       apply(subst alu_b_imm_de_ex[OF s'_de_valid])
       apply(simp add: decode_alu_b_imm Inst_LUI s'_inst_conv)

      apply(subst r1_de_ex'[OF s'_de_valid])
      apply(simp add: decode_rf_ra1 Inst_LUI s'_inst_conv)
      apply(simp add: read_rf_def)

      apply(subst imm32_de_ex_lui_ext[OF s'_de_valid])
       apply(simp add: decode_LUI_imm_ext_method Inst_LUI s'_inst_conv)
      apply(simp add: decode_imm16 Inst_LUI s'_inst_conv)

      apply(subst alu_op_de_ex[OF s'_de_valid])
      apply(simp add: decode_alu_op Inst_LUI s'_inst_conv)
      apply(simp add: alu_def)

      by (simp add: rf_conv_4_3')

    from Inst_LUI show ?thesis
      apply simp
      apply(rule mips.LUI)
      apply(simp add: proj_def)
      using not_jb_pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_J imm)
    have pc_correct:
      "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    mips.jump_dest (mips_pc (flush1 (flush1 (flush1 (flush1 s))))) imm"
      apply(simp add: mips.jump_dest_def)
      apply(subst s4_pc_conv)
      apply(subst flush1_same_pc[OF s'3_de_empty])
      apply(subst flush1_same_pc[OF s'2_de_empty])
      apply(subst flush1_same_pc[OF s'1_de_empty])
      apply(subst J_update_pc[OF s'_de_valid s'_no_stall])
       apply(simp add: decode_jump_imm_pc_sel Inst_J s'_inst_conv)

      apply(simp add: decode_imm26 Inst_J s'_inst_conv)
      apply(subst impl_step_inc_pc[OF s_no_stall s'_de_valid])

      by (rule refl)

    from Inst_J show ?thesis
      apply simp
      apply(rule mips.J)
      apply(simp add: proj_def)
      using pc_correct no_write_rf_correct not_store_dm_correct by simp
  next
    case (Inst_JAL imm)
    have pc_correct:
      "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    mips.jump_dest (mips_pc (flush1 (flush1 (flush1 (flush1 s))))) imm"
      apply(simp add: mips.jump_dest_def)
      apply(subst s4_pc_conv)
      apply(subst flush1_same_pc[OF s'3_de_empty])
      apply(subst flush1_same_pc[OF s'2_de_empty])
      apply(subst flush1_same_pc[OF s'1_de_empty])
      apply(subst J_update_pc[OF s'_de_valid s'_no_stall])
       apply(simp add: decode_jump_imm_pc_sel Inst_JAL s'_inst_conv)

      apply(simp add: decode_imm26 Inst_JAL s'_inst_conv)
      apply(subst impl_step_inc_pc[OF s_no_stall s'_de_valid])

      by (rule refl)

    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf 0x1F (mips.ret_addr (mips_pc (flush1 (flush1 (flush1 (flush1 s))))))
     (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst wb_pc_plus8)
       apply(subst rf_in_sel_mem_wb)
       apply(subst rf_in_sel_ex_mem)
       apply(subst rf_in_sel_de_ex[OF s'_de_valid])
       apply(simp add: decode_jal_rf_in_sel Inst_JAL s'_inst_conv)

      apply(subst rf_wa_mem_wb)
      apply(subst rf_wa_ex_mem)
      apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
      apply(simp add: decode_rf_wa Inst_JAL s'_inst_conv)

      apply(subst pc_mem_wb)
      apply(subst pc_ex_mem)
      apply(subst pc_de_ex)
      apply(subst impl_step_inc_pc[OF s_no_stall s'_de_valid])
      apply(simp add: mips.ret_addr_def)
      apply(subst s4_pc_conv)
      apply(simp add: rf_conv_4_3')
      apply(subgoal_tac \<open>2 + mips_pc s = mips_pc s + 2\<close>) apply(erule ssubst) apply(rule refl)
      by simp

    from Inst_JAL show ?thesis
      apply simp
      apply(rule mips.JAL)
      apply(simp add: proj_def)
      using pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_JR rs)
    have pc_correct:
      "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    slice 2 (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))"
      apply(subst flush1_same_pc[OF s'3_de_empty])
      apply(subst flush1_same_pc[OF s'2_de_empty])
      apply(subst flush1_same_pc[OF s'1_de_empty])
      apply(subst JR_update_pc[OF s'_de_valid s'_no_stall])
       apply(subst s'_inst_conv)
       apply(simp add: decode_jr_next_pc_sel Inst_JR)
      apply(subst s'_inst_conv)
      apply(subst rs_conv[OF s'_de_valid s'_no_stall])
       apply(simp add: s'_inst_conv)
      apply(simp add: decode_rf_ra1 Inst_JR s'_inst_conv)
      by (simp add: rf_conv_4_3')
    from Inst_JR show ?thesis apply simp
      apply(rule mips.JR)
      apply(simp add: proj_def)
      using pc_correct no_write_rf_correct not_store_dm_correct by simp
  next
    case (Inst_JALR rd rs)
    have pc_correct:
      "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    slice 2 (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))"
      apply(subst flush1_same_pc[OF s'3_de_empty])
      apply(subst flush1_same_pc[OF s'2_de_empty])
      apply(subst flush1_same_pc[OF s'1_de_empty])
      apply(subst JR_update_pc[OF s'_de_valid s'_no_stall])
       apply(subst s'_inst_conv)
       apply(simp add: decode_jr_next_pc_sel Inst_JALR)
      apply(subst s'_inst_conv)
      apply(subst rs_conv[OF s'_de_valid s'_no_stall])
       apply(simp add: s'_inst_conv)
      apply(simp add: decode_rf_ra1 Inst_JALR)
      by (simp add: rf_conv_4_3')
    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf rd (mips.ret_addr (mips_pc (flush1 (flush1 (flush1 (flush1 s))))))
     (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst wb_pc_plus8)
       apply(subst rf_in_sel_mem_wb)
       apply(subst rf_in_sel_ex_mem)
       apply(subst rf_in_sel_de_ex[OF s'_de_valid])
       apply(simp add: decode_jal_rf_in_sel s'_inst_conv Inst_JALR)

      apply(subst rf_wa_mem_wb)
      apply(subst rf_wa_ex_mem)
      apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
      apply(subst s'_inst_conv)
      apply(subst decode_rf_wa) apply(simp add: Inst_JALR) apply(simp add: Inst_JALR)

      apply(subst pc_de_wb)
      apply(simp add: mips.ret_addr_def)
      apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
      apply(subst s4_pc_conv)
      apply(subst rf_conv_4_3')
      apply(subgoal_tac \<open>2 + mips_pc s = mips_pc s + 2\<close>)
       apply(erule ssubst) apply(rule refl) by simp
    from Inst_JALR show ?thesis
      apply simp
      apply(rule mips.JALR)
      apply(simp add: proj_def)
      using pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_Branch op rs rt imm)
    show ?thesis
    proof(cases \<open>br_pred2_fn op (read_rf rs (Regs (proj (flush1 (flush1 (flush1 (flush1 s)))))))
     (read_rf rt (Regs (proj (flush1 (flush1 (flush1 (flush1 s)))))))\<close>)
      case True
      have pc_correct:
        "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    mips_pc (flush1 (flush1 (flush1 (flush1 s)))) + 1 + SCAST(16 \<rightarrow> 30) imm"
        apply(subst flush1_same_pc[OF s'3_de_empty])
        apply(subst flush1_same_pc[OF s'2_de_empty])
        apply(subst flush1_same_pc[OF s'1_de_empty])
        apply(cases op)
         apply(subst BEQ_update_pc[OF s'_de_valid s'_no_stall])
            apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch)
           apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch)
          apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
          apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
          apply(insert True)
          apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch)
          apply(simp add: proj_def)
          apply(simp add: rf_conv_4_3')
         apply(subst s4_pc_conv)
         apply(simp add: decode_imm16 s'_inst_conv Inst_Branch)
         apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        apply(subst BNE_update_pc[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch)
          apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch)
         apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch)
         apply(simp add: proj_def rf_conv_4_3')
        apply(subst s4_pc_conv)
        apply(simp add: decode_imm16 s'_inst_conv Inst_Branch)
        apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        done
      from Inst_Branch show ?thesis
        apply(simp)
        apply(rule mips.Branch_taken)
         apply(rule True)
        apply(simp add: proj_def)
        using pc_correct no_write_rf_correct not_store_dm_correct by simp
    next
      case False
      have pc_correct:
        "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    mips_pc (flush1 (flush1 (flush1 (flush1 s)))) + 1"
        apply(subst flush1_same_pc[OF s'3_de_empty])
        apply(subst flush1_same_pc[OF s'2_de_empty])
        apply(subst flush1_same_pc[OF s'1_de_empty])
        apply(cases op)
         apply(subst BEQ_update_pc_nt[OF s'_de_valid s'_no_stall])
            apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch)
           apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch)
          apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
          apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
          apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch)
          apply(insert False)
          apply(simp add: proj_def rf_conv_4_3')
         apply(subst s4_pc_conv)
         apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        apply(subst BNE_update_pc_nt[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch)
          apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch)
         apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch)
         apply(simp add: proj_def rf_conv_4_3')
        apply(subst s4_pc_conv)
        apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        done
      from Inst_Branch show ?thesis
        apply simp
        apply(rule mips.Branch_not_taken)
         apply(rule False)
        apply(simp add: proj_def)
        using pc_correct no_write_rf_correct not_store_dm_correct by simp
    qed

  next
    case (Inst_Branch1 op rs imm)
    show ?thesis
    proof(cases \<open>br_pred1_fn op (read_rf rs (Regs (proj (flush1 (flush1 (flush1 (flush1 s)))))))\<close>)
      case True
      have pc_correct:
        "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    mips_pc (flush1 (flush1 (flush1 (flush1 s)))) + 1 + SCAST(16 \<rightarrow> 30) imm"
        apply(subst flush1_same_pc[OF s'3_de_empty])
        apply(subst flush1_same_pc[OF s'2_de_empty])
        apply(subst flush1_same_pc[OF s'1_de_empty])
        apply(cases op)
         apply(subst BLEZ_update_pc[OF s'_de_valid s'_no_stall])
            apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch1)
           apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch1)
          apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
          apply(insert True)
          apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch1)
          apply(simp add: proj_def)
          apply(simp add: rf_conv_4_3')
         apply(subst s4_pc_conv)
         apply(simp add: decode_imm16 s'_inst_conv Inst_Branch1)
         apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        apply(subst BGTZ_update_pc[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch1)
          apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch1)
         apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch1)
         apply(simp add: proj_def rf_conv_4_3')
        apply(subst s4_pc_conv)
        apply(simp add: decode_imm16 s'_inst_conv Inst_Branch1)
        apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        done
      from Inst_Branch1 show ?thesis
        apply(simp)
        apply(rule mips.Branch1_taken)
         apply(rule True)
        apply(simp add: proj_def)
        using pc_correct no_write_rf_correct not_store_dm_correct by simp
    next
      case False
      have pc_correct:
        "mips_pc (flush1 (flush1 (flush1 (flush1 (impl_step im s))))) =
    mips_pc (flush1 (flush1 (flush1 (flush1 s)))) + 1"
        apply(subst flush1_same_pc[OF s'3_de_empty])
        apply(subst flush1_same_pc[OF s'2_de_empty])
        apply(subst flush1_same_pc[OF s'1_de_empty])
        apply(cases op)
         apply(subst BLEZ_update_pc_nt[OF s'_de_valid s'_no_stall])
            apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch1)
           apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch1)
          apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
          apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch1)
          apply(insert False)
          apply(simp add: proj_def rf_conv_4_3')
         apply(subst s4_pc_conv)
         apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        apply(subst BGTZ_update_pc_nt[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_br_pc_sel s'_inst_conv Inst_Branch1)
          apply(simp add: decode_cond_sel s'_inst_conv Inst_Branch1)
         apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(simp add: decode_rf_ra1 decode_rf_ra2 s'_inst_conv Inst_Branch1)
         apply(simp add: proj_def rf_conv_4_3')
        apply(subst s4_pc_conv)
        apply(simp add: impl_step_inc_pc[OF s_no_stall s'_de_valid])
        done
      from Inst_Branch1 show ?thesis
        apply simp
        apply(rule mips.Branch1_not_taken)
         apply(rule False)
        apply(simp add: proj_def)
        using pc_correct no_write_rf_correct not_store_dm_correct by simp
    qed
  next
    case (Inst_Load sz sign rt rs imm)
    have rf_correct:
      "regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    write_rf rt
     (mips.load_ext load
            (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))) +
             mips.sext imm)
            sz sign (dmem_m (mips_dm (flush1 (flush1 (flush1 (flush1 s)))))))
     (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(cases sz)
        apply(cases sign)
\<comment> \<open>LB\<close>
         apply(subst wb_lb)
            apply(subst rf_in_sel_mem_wb)
            apply(subst rf_in_sel_ex_mem)
            apply(subst rf_in_sel_de_ex[OF s'_de_valid])
            apply(simp add: decode_load_rf_in_sel Inst_Load s'_inst_conv)

           apply(subst dm_req_size_mem_wb)
           apply(subst dm_req_size_ex_mem)
           apply(subst dm_req_size_de_ex[OF s'_de_valid])
           apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

          apply(subst mem_data_sign_ext_mem_wb)
          apply(subst mem_data_sign_ext_ex_mem)
          apply(subst mem_data_sign_ext_de_ex[OF s'_de_valid])
          apply(simp add: decode_mem_data_sign_ext Inst_Load s'_inst_conv)

         apply(subst rf_wa_mem_wb)
         apply(subst rf_wa_ex_mem)
         apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
         apply(simp add: decode_rf_wa Inst_Load s'_inst_conv)

         apply(simp add: mips.load_ext_def load_def)
         apply(subst dm_out_mem_wb_lb)
            apply(subst dm_en_ex_mem)
            apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
            apply(simp add: decode_ls_dm_en Inst_Load s'_inst_conv)
           apply(subst dm_wr_ex_mem)
           apply(subst dm_wr_de_ex[OF s'_de_valid])
           apply(simp add: decode_load_dm_wr Inst_Load s'_inst_conv)

          apply(subst dm_req_size_ex_mem)
          apply(subst dm_req_size_de_ex[OF s'_de_valid])
          apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

         apply(subst dm_unchanged[OF s3_mem_empty])
         apply(subst dmem_conv_3_2'[of s im])

         apply(subst alu_out_ex_mem_imm)
          apply(subst alu_b_imm_de_ex[OF s'_de_valid])
          apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)

         apply(subst r1_de_ex'[OF s'_de_valid])
         apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)

         apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
          apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)

         apply(simp add: decode_imm16 Inst_Load s'_inst_conv)

         apply(subst alu_op_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_op Inst_Load s'_inst_conv)
         apply(simp add: alu_def)
         apply(simp add: mips.sext_def)
         apply (simp add: rf_conv_4_3')

\<comment> \<open>LBU\<close>
         apply(subst wb_lbu)
            apply(subst rf_in_sel_mem_wb)
            apply(subst rf_in_sel_ex_mem)
            apply(subst rf_in_sel_de_ex[OF s'_de_valid])
            apply(simp add: decode_load_rf_in_sel Inst_Load s'_inst_conv)

           apply(subst dm_req_size_mem_wb)
           apply(subst dm_req_size_ex_mem)
           apply(subst dm_req_size_de_ex[OF s'_de_valid])
           apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

          apply(subst mem_data_sign_ext_mem_wb)
          apply(subst mem_data_sign_ext_ex_mem)
          apply(subst mem_data_sign_ext_de_ex[OF s'_de_valid])
          apply(simp add: decode_mem_data_sign_ext Inst_Load s'_inst_conv)

         apply(subst rf_wa_mem_wb)
         apply(subst rf_wa_ex_mem)
         apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
         apply(simp add: decode_rf_wa Inst_Load s'_inst_conv)

         apply(simp add: mips.load_ext_def load_def)
         apply(subst dm_out_mem_wb_lb)
            apply(subst dm_en_ex_mem)
            apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
            apply(simp add: decode_ls_dm_en Inst_Load s'_inst_conv)
           apply(subst dm_wr_ex_mem)
           apply(subst dm_wr_de_ex[OF s'_de_valid])
           apply(simp add: decode_load_dm_wr Inst_Load s'_inst_conv)

          apply(subst dm_req_size_ex_mem)
          apply(subst dm_req_size_de_ex[OF s'_de_valid])
          apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

         apply(subst dm_unchanged[OF s3_mem_empty])
         apply(subst dmem_conv_3_2'[of s im])

         apply(subst alu_out_ex_mem_imm)
          apply(subst alu_b_imm_de_ex[OF s'_de_valid])
          apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)

         apply(subst r1_de_ex'[OF s'_de_valid])
         apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
         apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)

         apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
          apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)

         apply(simp add: decode_imm16 Inst_Load s'_inst_conv)

         apply(subst alu_op_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_op Inst_Load s'_inst_conv)
         apply(simp add: alu_def)
         apply(simp add: mips.sext_def)
         apply (simp add: rf_conv_4_3')

       apply(cases sign)
\<comment> \<open>LH\<close>
        apply(subst wb_lh)
           apply(subst rf_in_sel_mem_wb)
           apply(subst rf_in_sel_ex_mem)
           apply(subst rf_in_sel_de_ex[OF s'_de_valid])
           apply(simp add: decode_load_rf_in_sel Inst_Load s'_inst_conv)

          apply(subst dm_req_size_mem_wb)
          apply(subst dm_req_size_ex_mem)
          apply(subst dm_req_size_de_ex[OF s'_de_valid])
          apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

         apply(subst mem_data_sign_ext_mem_wb)
         apply(subst mem_data_sign_ext_ex_mem)
         apply(subst mem_data_sign_ext_de_ex[OF s'_de_valid])
         apply(simp add: decode_mem_data_sign_ext Inst_Load s'_inst_conv)

        apply(subst rf_wa_mem_wb)
        apply(subst rf_wa_ex_mem)
        apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
        apply(simp add: decode_rf_wa Inst_Load s'_inst_conv)

        apply(simp add: mips.load_ext_def load_def)
        apply(subst dm_out_mem_wb_lh)
           apply(subst dm_en_ex_mem)
           apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_ls_dm_en Inst_Load s'_inst_conv)
          apply(subst dm_wr_ex_mem)
          apply(subst dm_wr_de_ex[OF s'_de_valid])
          apply(simp add: decode_load_dm_wr Inst_Load s'_inst_conv)

         apply(subst dm_req_size_ex_mem)
         apply(subst dm_req_size_de_ex[OF s'_de_valid])
         apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])
        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(simp add: decode_imm16 Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(simp add: alu_def)
        apply(simp add: mips.sext_def Let_def)
        apply (simp add: rf_conv_4_3')

\<comment> \<open>LHU\<close>
        apply(subst wb_lhu)
           apply(subst rf_in_sel_mem_wb)
           apply(subst rf_in_sel_ex_mem)
           apply(subst rf_in_sel_de_ex[OF s'_de_valid])
           apply(simp add: decode_load_rf_in_sel Inst_Load s'_inst_conv)

          apply(subst dm_req_size_mem_wb)
          apply(subst dm_req_size_ex_mem)
          apply(subst dm_req_size_de_ex[OF s'_de_valid])
          apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

         apply(subst mem_data_sign_ext_mem_wb)
         apply(subst mem_data_sign_ext_ex_mem)
         apply(subst mem_data_sign_ext_de_ex[OF s'_de_valid])
         apply(simp add: decode_mem_data_sign_ext Inst_Load s'_inst_conv)

        apply(subst rf_wa_mem_wb)
        apply(subst rf_wa_ex_mem)
        apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
        apply(simp add: decode_rf_wa Inst_Load s'_inst_conv)

        apply(simp add: mips.load_ext_def load_def)
        apply(subst dm_out_mem_wb_lh)
           apply(subst dm_en_ex_mem)
           apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_ls_dm_en Inst_Load s'_inst_conv)
          apply(subst dm_wr_ex_mem)
          apply(subst dm_wr_de_ex[OF s'_de_valid])
          apply(simp add: decode_load_dm_wr Inst_Load s'_inst_conv)

         apply(subst dm_req_size_ex_mem)
         apply(subst dm_req_size_de_ex[OF s'_de_valid])
         apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])
        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(simp add: decode_imm16 Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(simp add: alu_def)
        apply(simp add: mips.sext_def Let_def)
        apply (simp add: rf_conv_4_3')
\<comment> \<open>LW\<close>
        apply(subst wb_lw)
           apply(subst rf_in_sel_mem_wb)
           apply(subst rf_in_sel_ex_mem)
           apply(subst rf_in_sel_de_ex[OF s'_de_valid])
           apply(simp add: decode_load_rf_in_sel Inst_Load s'_inst_conv)

          apply(subst dm_req_size_mem_wb)
          apply(subst dm_req_size_ex_mem)
          apply(subst dm_req_size_de_ex[OF s'_de_valid])
          apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

        apply(subst rf_wa_mem_wb)
        apply(subst rf_wa_ex_mem)
        apply(subst rf_wa_de_ex[OF s'_de_valid s'_no_stall])
        apply(simp add: decode_rf_wa Inst_Load s'_inst_conv)

        apply(simp add: mips.load_ext_def load_def)
        apply(subst dm_out_mem_wb_lw)
           apply(subst dm_en_ex_mem)
           apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
           apply(simp add: decode_ls_dm_en Inst_Load s'_inst_conv)
          apply(subst dm_wr_ex_mem)
          apply(subst dm_wr_de_ex[OF s'_de_valid])
          apply(simp add: decode_load_dm_wr Inst_Load s'_inst_conv)

         apply(subst dm_req_size_ex_mem)
         apply(subst dm_req_size_de_ex[OF s'_de_valid])
         apply(simp add: decode_dm_req_size Inst_Load s'_inst_conv)

        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])
        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])
        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])
        apply(subst dm_unchanged[OF s3_mem_empty])
        apply(subst dmem_conv_3_2'[of s im])

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(simp add: decode_imm16 Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(subst alu_out_ex_mem_imm)
         apply(subst alu_b_imm_de_ex[OF s'_de_valid])
         apply(simp add: decode_alu_b_imm Inst_Load s'_inst_conv)
        apply(subst r1_de_ex'[OF s'_de_valid])
        apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
        apply(simp add: decode_rf_ra1 Inst_Load s'_inst_conv)
        apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
         apply(simp add: decode_ls_imm_ext_method Inst_Load s'_inst_conv)
        apply(simp add: decode_imm16 Inst_Load s'_inst_conv)
        apply(subst alu_op_de_ex[OF s'_de_valid])
        apply(simp add: decode_alu_op Inst_Load s'_inst_conv)

        apply(simp add: alu_def)
        apply(simp add: mips.sext_def Let_def)
      by (simp add: rf_conv_4_3')

    from Inst_Load show ?thesis
      apply simp
      apply(rule mips.Load)
      apply(simp add: proj_def)
      using not_jb_pc_correct rf_correct not_store_dm_correct by simp
  next
    case (Inst_Store sz rt rs imm)
    have dm_correct:
"dmem_m (mips_dm (flush1 (flush1 (flush1 (flush1 (impl_step im s)))))) =
    store
     (read_rf rs (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))) + mips.sext imm) sz
     (read_rf rt (regfile_r (mips_rf (flush1 (flush1 (flush1 (flush1 s)))))))
     (dmem_m (mips_dm (flush1 (flush1 (flush1 (flush1 s))))))"
      apply(subst dm_unchanged[OF s'3_mem_empty])
      apply(subst dm_unchanged[OF s3_mem_empty])
      apply(subst store_update_dm)
      apply(subst dm_en_ex_mem)
        apply(subst dm_en_de_ex[OF s'_de_valid s'_no_stall])
        apply(simp add: decode_ls_dm_en Inst_Store s'_inst_conv)
       apply(subst dm_wr_ex_mem)
       apply(subst dm_wr_de_ex[OF s'_de_valid])
       apply(simp add: decode_store_dm_wr Inst_Store s'_inst_conv)
      apply(subst alu_out_ex_mem_imm)
       apply(subst alu_b_imm_de_ex[OF s'_de_valid])
       apply(simp add: decode_alu_b_imm Inst_Store s'_inst_conv)
      apply(subst r1_de_ex'[OF s'_de_valid])
      apply(subst rs_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
      apply(simp add: decode_rf_ra1 Inst_Store s'_inst_conv)
      apply(subst imm32_de_ex_sign_ext[OF s'_de_valid])
      apply(simp add: decode_ls_imm_ext_method Inst_Store s'_inst_conv)
      apply(simp add: decode_imm16 Inst_Store s'_inst_conv)
      apply(subst alu_op_de_ex[OF s'_de_valid])
      apply(simp add: decode_alu_op Inst_Store s'_inst_conv)
      apply(subst dm_req_size_ex_mem)
      apply(subst dm_req_size_de_ex[OF s'_de_valid])
      apply(simp add: decode_dm_req_size Inst_Store s'_inst_conv)
      apply(subst dm_in_ex_mem)
      apply(subst r2_de_ex'[OF s'_de_valid])
      apply(subst rt_conv[OF s'_de_valid s'_no_stall]) apply(rule refl)
      apply(simp add: decode_rf_ra2 Inst_Store s'_inst_conv)
      apply(simp add: alu_def mips.sext_def)
      apply(simp add: rf_conv_4_3')
      apply(simp add: dmem_conv_3_2'[of s im])
      apply(cases sz; simp)
      done
    from Inst_Store show ?thesis
      apply simp
      apply(rule mips.Store)
      apply(simp add: proj_def)
      using not_jb_pc_correct no_write_rf_correct dm_correct by simp
  next
    case Inst_Undef
    then show ?thesis
      apply simp
      by (rule mips.Undef)
  qed
  moreover
  {
    have \<open>proj (flush s) = proj (flush1 (flush1 (flush1 (flush1 s))))\<close> using abstract_eq[OF s_no_stall] .
    then have \<open>PC (proj (flush s)) = mips_pc s\<close> by (simp add: s4_pc_conv proj_def)
  }
  ultimately show \<open>mips.isa_step load store (proj (flush s)) (mips.decode (im (PC (proj (flush s))))) (proj (flush (impl_step im s)))\<close>
    using abstract_eq[OF s_no_stall] abstract_eq[OF s'_no_stall] by simp
qed

lemma de_empty_imp_next_ex_empty':
  \<open>\<not> mips_de_valid s \<Longrightarrow> ex_empty (impl_step im s)\<close>
  by (simp add: impl_step_def mips_upd_def Let_def)

lemma de_empty_imp_next_de_valid':
  \<open>\<not> mips_de_valid s \<Longrightarrow> mips_de_valid (impl_step im s)\<close>
  by (simp add: impl_step_def mips_upd_def Let_def data_hazard_def eqnz_def)

lemma rf_out1_no_write_conv:
  \<open>regfile_out_out1 ra 0 d s = regfile_out_out1 ra 0 d' s\<close>
  by (simp add: regfile_out_out1_def)

lemma rf_out2_no_write_conv:
  \<open>regfile_out_out2 ra 0 d s = regfile_out_out2 ra 0 d' s\<close>
  by (simp add: regfile_out_out2_def)

lemma flush1_same_pc_de_empty:
  \<open>mips_pc s1 = mips_pc s2 \<Longrightarrow> \<not> mips_de_valid s1 \<Longrightarrow> \<not> mips_de_valid s2 \<Longrightarrow>
   mips_pc (flush1 s1) = mips_pc (flush1 s2)\<close>
  by (simp add: flush1_def mips_upd_def Let_def data_hazard_def eqnz_def next_pc_def)

lemma rf_no_write_conv:
  \<open>regfile_upd 0 d rf = rf\<close>
  by (simp add: regfile_upd_def)

lemma dm_no_en_conv:
  \<open>dmem_upd False wr a sz d dm = dm\<close>
  by (simp add: dmem_upd_def)

lemma same_stall:
  \<open>\<not> mips_de_valid s1 \<and> \<not> mips_de_valid s2 \<or>
   mips_de_valid s1 \<and> mips_de_valid s2 \<and> mips_inst s1 = mips_inst s2 \<Longrightarrow>
   \<not> ExecuteStage_dm_en (mips_ex s1) \<and>
   ExecuteStage_rf_wa (mips_ex s1) = 0 \<and>
   \<not> ExecuteStage_dm_en (mips_ex s2) \<and> ExecuteStage_rf_wa (mips_ex s2) = 0 \<or>
   mips_ex s1 = mips_ex s2 \<Longrightarrow>
   \<not> MemoryStage_dm_en (mips_mem s1) \<and>
   MemoryStage_rf_wa (mips_mem s1) = 0 \<and>
   \<not> MemoryStage_dm_en (mips_mem s2) \<and> MemoryStage_rf_wa (mips_mem s2) = 0 \<or>
   mips_mem s1 = mips_mem s2 \<Longrightarrow>
   stall s1 = stall s2\<close>
  apply(subgoal_tac \<open>ExecuteStage_rf_wa (mips_ex s1) = ExecuteStage_rf_wa (mips_ex s2)\<close>)
   prefer 2 apply(cases \<open>mips_ex s1 = mips_ex s2\<close>; simp)
  apply(subgoal_tac \<open>MemoryStage_rf_wa (mips_mem s1) = MemoryStage_rf_wa (mips_mem s2)\<close>)
   prefer 2 apply(cases \<open>mips_mem s1 = mips_mem s2\<close>; simp)
  apply(simp add: stall_def Let_def)
  apply(cases \<open>mips_de_valid s1\<close>; simp)
  done

lemma flush1_sim:
  \<open>mips_state_sim s1 s2 \<Longrightarrow> mips_state_sim (flush1 s1) (flush1 s2)\<close>
  apply(simp add: mips_state_sim_def Let_def)
  apply clarify
  apply(rule conjI)
   apply(cases \<open>mips_de_valid s1\<close>; simp)
    apply(cases \<open>WritebackStage_rf_wa (mips_wb s1) = 0 \<and> WritebackStage_rf_wa (mips_wb s2) = 0\<close>; simp)
     apply(simp add: flush1_def mips_upd_def Let_def)
     apply(simp add: rf_out1_no_write_conv
      [where d=\<open>rf_in (mips_wb s1) (dmem_out_out (mips_dm s2))\<close> and d'=\<open>rf_in (mips_wb s2) (dmem_out_out (mips_dm s2))\<close>]
      rf_out2_no_write_conv
      [where d=\<open>rf_in (mips_wb s1) (dmem_out_out (mips_dm s2))\<close> and d'=\<open>rf_in (mips_wb s2) (dmem_out_out (mips_dm s2))\<close>])
     apply presburger

    apply(simp add: flush1_def mips_upd_def Let_def)
    apply presburger

  using flush1_same_pc_de_empty apply blast

  apply(rule conjI)
   apply(simp add: flush1_def mips_upd_def Let_def)
   apply(cases \<open>mips_wb s1 = mips_wb s2\<close>; simp)
   apply(simp add: rf_no_write_conv)

  apply(rule conjI)
   apply(simp add: flush1_def mips_upd_def Let_def)
   apply(cases \<open>mips_mem s1 = mips_mem s2\<close>; simp)
   apply(simp add: dm_no_en_conv)

  apply(subgoal_tac \<open>stall s1 = stall s2\<close>) prefer 2 using same_stall apply auto[1]

  apply(rule conjI)
   apply(cases \<open>\<not> mips_de_valid s1 \<and> \<not> mips_de_valid s2\<close>; simp)
  using de_empty_imp_next_de_empty apply presburger
   apply(cases \<open>stall s1\<close>; simp)
  using stall_imp_next_de_valid stall_imp_inst_unchanged apply presburger
   apply(subgoal_tac \<open>\<not> stall s2\<close>)
    prefer 2 apply(simp add: stall_def Let_def)
  using no_stall_imp_next_de_empty apply presburger

  apply(rule conjI)
   apply(cases \<open>stall s1\<close>; simp)
  using stall_imp_next_ex_empty[simplified] apply metis
   apply(cases \<open>mips_de_valid s1\<close>; simp)
    apply(rule disjI2)
    apply(simp add: flush1_def mips_upd_def Let_def stall_def)
    apply(cases \<open>mips_wb s1 = mips_wb s2\<close>; simp)
  using rf_out1_no_write_conv rf_out2_no_write_conv apply presburger
  using de_empty_imp_next_ex_empty[simplified] apply metis

  apply(rule conjI)
   apply(cases \<open>mips_ex s1 = mips_ex s2\<close>; simp)
    apply(rule disjI2)
    apply(simp add: flush1_def mips_upd_def Let_def)
  using ex_empty_imp_next_mem_empty[simplified] apply metis

  apply(cases \<open>mips_mem s1 = mips_mem s2\<close>; simp)
   apply(rule disjI2)
   apply(simp add: flush1_def mips_upd_def Let_def)
  using mem_empty_imp_next_wb_empty[simplified] apply metis

  done

lemma sim_imp_same_proj:
  \<open>mips_state_sim s1 s2 \<Longrightarrow> proj s1 = proj s2\<close>
  by (simp add: mips_state_sim_def proj_def)

lemma sim_imp_same_abstract:
  \<open>mips_state_sim s1 s2 \<Longrightarrow> abstract s1 = abstract s2\<close>
  apply(subgoal_tac \<open>mips_de_valid s1 = mips_de_valid s2\<close>)
   prefer 2 apply(simp add: mips_state_sim_def) apply blast
  apply(simp add: abstract_def flush_def)
  apply(cases \<open>mips_de_valid s1\<close>; simp)
   apply(simp add: run_until_no_stall_def)
   apply(subgoal_tac \<open>stall s1 = stall s2\<close>)
    prefer 2 apply(simp add: mips_state_sim_def Let_def)
    apply(rule same_stall) apply blast apply blast apply blast
   apply(cases \<open>stall s1\<close>; simp add: Let_def)
    apply(frule flush1_sim)
    apply(subgoal_tac \<open>stall (flush1 s1) = stall (flush1 s2)\<close>)
     prefer 2 apply(simp add: mips_state_sim_def Let_def)
     apply(rule same_stall) apply blast apply blast apply blast
    apply(cases \<open>stall (flush1 s1)\<close>; simp)
     apply(simp add: flush_till_ex_def)
  using flush1_sim sim_imp_same_proj apply presburger
    apply(simp add: flush_till_ex_def)
  using flush1_sim sim_imp_same_proj apply presburger
   apply(simp add: flush_till_ex_def)
  using flush1_sim sim_imp_same_proj apply presburger
  apply(simp add: flush_till_ex_def)
  using flush1_sim sim_imp_same_proj apply presburger
  done

lemma next_rf':
  \<open>regfile_r (mips_rf (impl_step im s)) = write_rf (WritebackStage_rf_wa (mips_wb s)) (rf_in (mips_wb s) (dmem_out_out (mips_dm s))) (regfile_r (mips_rf s))\<close>
  by (simp add: impl_step_def mips_upd_def Let_def regfile_upd_def write_rf_def)

lemma flushed_imp_flush1_sim:
  \<open>flushed s \<Longrightarrow> mips_state_sim (flush1 s) s\<close>
  by (simp add: flushed_def mips_state_sim_def flush1_def mips_upd_def Let_def data_hazard_def eqnz_def next_pc_def regfile_upd_def dmem_upd_def)

lemma flush_de_empty':
  \<open>\<not> mips_de_valid s \<Longrightarrow> flush s = flush1 (flush1 (flush1 s))\<close>
  using flush_de_empty flush_till_ex_def by force

lemma no_stall_imp_next_no_stall:
  \<open>\<not> stall s \<Longrightarrow> \<not> stall (flush1 s)\<close>
  by (auto simp add: stall_def flush1_def mips_upd_def Let_def; simp add: data_hazard_def eqnz_def)

lemma flush2_no_stall:
  \<open>\<not> stall (flush1 (flush1 s))\<close>
  apply(cases \<open>stall s\<close>)
   apply(cases \<open>stall (flush1 s)\<close>)
  apply(subgoal_tac \<open>mem_empty (flush1 (flush1 s))\<close>)
     apply(subgoal_tac \<open>ex_empty (flush1 (flush1 s))\<close>)
  using ex_and_mem_empty_imp_no_stall apply blast
  using stall_imp_next_ex_empty apply blast
  apply(rule ex_empty_imp_next_mem_empty)
  using stall_imp_next_ex_empty apply blast
   apply(erule no_stall_imp_next_no_stall)
  apply(drule no_stall_imp_next_no_stall)
  apply(erule no_stall_imp_next_no_stall)
  done

lemma sim_refl:
  \<open>mips_state_sim s s\<close>
  by (simp add: mips_state_sim_def)

lemma sim_sym:
  \<open>mips_state_sim s1 s2 \<Longrightarrow> mips_state_sim s2 s1\<close>
  apply(simp add: mips_state_sim_def Let_def)
  apply(rule conjI) apply argo
  apply(rule conjI) apply metis
  apply(rule conjI) apply metis
  by metis

lemma sim_trans:
  \<open>mips_state_sim s1 s2 \<Longrightarrow> mips_state_sim s2 s3 \<Longrightarrow> mips_state_sim s1 s3\<close>
  apply(simp add: mips_state_sim_def Let_def)
  apply(rule conjI) apply argo
  apply(rule conjI) apply metis
  apply(rule conjI) apply metis
  by metis

lemma flush_conv_stall2:
  \<open>stall s \<Longrightarrow> stall (flush s) \<Longrightarrow> flush s = flush1 (flush1 (flush1 (flush1 (flush1 (flush1 s)))))\<close>
  apply(auto simp add: flush_def)
  using de_empty_imp_no_stall apply blast
  apply(simp add: flush_till_ex_def)
  using flush2_no_stall apply blast
  done

(* Why do I have to write such a long proof for something so obvious? *)
lemma flush_flush1_sim:
  \<open>mips_state_sim (flush (flush1 s)) (flush s)\<close>
  apply(auto simp add: flush_def flush_till_ex_def)
     apply(subgoal_tac \<open>flush1 (flush1 (flush1 (flush1 s))) = flush1 (flush s)\<close>)
      apply(erule ssubst)
      apply(subst flush_de_empty'[symmetric]) apply assumption
      apply(rule flushed_imp_flush1_sim)
      apply(rule flush_correct)
  using flush_de_empty' apply simp
    apply(simp add: run_until_no_stall_def Let_def)
    apply auto[1]
  using de_empty_imp_no_stall apply blast
  using de_empty_imp_no_stall apply blast
  using stall_imp_next_de_valid apply blast
    apply(rule sim_refl)
   apply(simp add: run_until_no_stall_def Let_def)
   apply auto[1]
  using de_empty_imp_next_de_empty apply blast
  using de_empty_imp_next_de_empty apply blast
  using de_empty_imp_next_de_empty apply blast
  using de_empty_imp_next_de_empty apply blast
   apply(simp add: run_until_no_stall_def Let_def)
   apply auto[1]
  using flush2_no_stall apply blast
  using flush2_no_stall apply blast
  using flush2_no_stall apply blast
  using flush2_no_stall apply blast
     apply(rule sim_refl)
  using no_stall_imp_next_no_stall apply blast
   apply(rule sim_refl)
  using no_stall_imp_next_de_empty apply blast
  done

lemma sim_s'1_s1':
  assumes s_no_stall: \<open>\<not> stall s\<close>
    and s'_de_valid: \<open>mips_de_valid (impl_step im s)\<close>
    and s'_stall: \<open>stall (impl_step im s)\<close>
    and s'1_no_stall: \<open>\<not> stall (flush1 (impl_step im s))\<close>
  shows \<open>mips_state_sim (flush1 (impl_step im s)) (impl_step im (flush1 s))\<close>
proof-
  let ?s' = \<open>impl_step im s\<close>
  let ?s1 = \<open>flush1 s\<close>
  let ?s1' = \<open>impl_step im ?s1\<close>
  let ?s'1 = \<open>flush1 ?s'\<close>
  have s1_de_empty: \<open>\<not> mips_de_valid ?s1\<close> using no_stall_imp_next_de_empty[OF s_no_stall] .
  have s1_no_stall: \<open>\<not> stall ?s1\<close> using de_empty_imp_no_stall[OF s1_de_empty] .
  have s1'_ex_empty: \<open>ex_empty ?s1'\<close> using de_empty_imp_next_ex_empty'[OF s1_de_empty] .
  have s1'_de_valid: \<open>mips_de_valid ?s1'\<close> using de_empty_imp_next_de_valid'[OF s1_de_empty] .
  have s'1_ex_empty: \<open>ex_empty ?s'1\<close> using stall_imp_next_ex_empty[OF s'_stall] .
  have s'1_de_valid: \<open>mips_de_valid ?s'1\<close> using stall_imp_next_de_valid[OF s'_stall] .
  have wb_conv: \<open>mips_wb ?s'1 = mips_wb ?s1'\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have mem_conv: \<open>mips_mem ?s'1 = mips_mem ?s1'\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have inst_conv: \<open>mips_inst ?s'1 = mips_inst ?s1'\<close>
    apply(subst stall_imp_inst_unchanged[OF s'_stall])
    apply(simp add: impl_step_def mips_out_im_addr_def)
    apply(subst flush1_same_pc2[OF s'_de_valid])
    using s_no_stall by (auto simp add: mips_upd_def Let_def s1_de_empty data_hazard_def eqnz_def stall_def)
  have wb_conv_s'_s1: \<open>mips_wb ?s' = mips_wb ?s1\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have rf_conv_s'_s1: \<open>mips_rf ?s' = mips_rf ?s1\<close>
    apply(subgoal_tac \<open>regfile_r (mips_rf (impl_step im s)) = regfile_r (mips_rf (flush1 s))\<close>)
    apply simp
    by (simp add: next_rf next_rf')
  have dm_conv_s'_s1: \<open>mips_dm ?s' = mips_dm ?s1\<close>
    by (simp add: impl_step_def flush1_def mips_upd_def Let_def)
  show ?thesis
    apply(simp add: mips_state_sim_def Let_def)
    apply(rule conjI)
     apply(subst stall_pc_unchanged[OF s'_stall])
     apply(subst impl_step_inc_pc[OF s_no_stall s'_de_valid])
     apply(subst impl_step_inc_pc[OF s1_no_stall s1'_de_valid])
     apply(subst flush1_same_pc2[OF s'_de_valid])
     apply(rule refl)
    apply(rule conjI)
     apply(subgoal_tac \<open>regfile_r (mips_rf (flush1 (impl_step im s))) = regfile_r (mips_rf (impl_step im (flush1 s)))\<close>)
      apply simp
     apply(subst next_rf)
    apply(subst next_rf'[of im "flush1 s"])
     apply(simp add: wb_conv_s'_s1 rf_conv_s'_s1 dm_conv_s'_s1)
    apply(rule conjI)
     apply(simp add: flush1_def impl_step_def mips_upd_def Let_def)
    apply(rule conjI)
    using s'1_de_valid s1'_de_valid inst_conv apply blast
    apply(rule conjI)
    using s'1_ex_empty[simplified] s1'_ex_empty[simplified] apply metis
    apply(rule conjI)
    apply(rule disjI2)
     apply(simp add: flush1_def impl_step_def mips_upd_def Let_def)
    apply(rule disjI2)
    apply(simp add: flush1_def impl_step_def mips_upd_def Let_def)
    done
qed

lemma abstract_conv_stall1:
  assumes s_no_stall: \<open>\<not> stall s\<close>
    and s'_de_valid: \<open>mips_de_valid (impl_step im s)\<close>
    and s'_stall: \<open>stall (impl_step im s)\<close>
    and s'1_no_stall: \<open>\<not> stall (flush1 (impl_step im s))\<close>
  shows \<open>abstract (impl_step im s) = abstract (impl_step im (flush1 s))\<close>
proof-
  have \<open>proj (flush (flush1 (impl_step im s))) = proj (flush (impl_step im s))\<close>
    apply(rule sim_imp_same_proj)
    by (rule flush_flush1_sim)
  then show ?thesis using sim_imp_same_abstract[OF sim_s'1_s1'[OF s_no_stall s'_de_valid s'_stall s'1_no_stall]]
    by (simp add: abstract_def)
qed

lemma next_dm:
  \<open>mips_dm (flush1 s) =
     dmem_upd (MemoryStage_dm_en (mips_mem s)) (MemoryStage_dm_wr (mips_mem s)) (MemoryStage_alu_out (mips_mem s))
     (MemoryStage_dm_req_size (mips_mem s)) (MemoryStage_dm_in (mips_mem s)) (mips_dm s)\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma next_dm':
  \<open>mips_dm (impl_step im s) =
     dmem_upd (MemoryStage_dm_en (mips_mem s)) (MemoryStage_dm_wr (mips_mem s)) (MemoryStage_alu_out (mips_mem s))
     (MemoryStage_dm_req_size (mips_mem s)) (MemoryStage_dm_in (mips_mem s)) (mips_dm s)\<close>
  by (simp add: impl_step_def mips_upd_def Let_def)

lemma next_wb:
  \<open>mips_wb (flush1 s) = \<lparr>WritebackStage_alu_out = MemoryStage_alu_out (mips_mem s),
       WritebackStage_shifter_out = MemoryStage_shifter_out (mips_mem s),
       WritebackStage_rf_wa = MemoryStage_rf_wa (mips_mem s),
       WritebackStage_rf_in_sel = MemoryStage_rf_in_sel (mips_mem s),
       WritebackStage_dm_req_size = MemoryStage_dm_req_size (mips_mem s),
       WritebackStage_mem_data_sign_ext = MemoryStage_mem_data_sign_ext (mips_mem s),
       WritebackStage_pc = MemoryStage_pc (mips_mem s)\<rparr>\<close>
  by (simp add: flush1_def mips_upd_def Let_def)

lemma next_wb':
  \<open>mips_wb (impl_step im s) = \<lparr>WritebackStage_alu_out = MemoryStage_alu_out (mips_mem s),
       WritebackStage_shifter_out = MemoryStage_shifter_out (mips_mem s),
       WritebackStage_rf_wa = MemoryStage_rf_wa (mips_mem s),
       WritebackStage_rf_in_sel = MemoryStage_rf_in_sel (mips_mem s),
       WritebackStage_dm_req_size = MemoryStage_dm_req_size (mips_mem s),
       WritebackStage_mem_data_sign_ext = MemoryStage_mem_data_sign_ext (mips_mem s),
       WritebackStage_pc = MemoryStage_pc (mips_mem s)\<rparr>\<close>
  by (simp add: impl_step_def mips_upd_def Let_def)

lemma abstract_conv_stall2:
  assumes s_no_stall: \<open>\<not> stall s\<close>
    and s'_de_valid: \<open>mips_de_valid (impl_step im s)\<close>
    and s'_stall: \<open>stall (impl_step im s)\<close>
    and s'1_stall: \<open>stall (flush1 (impl_step im s))\<close>
    and s'2_no_stall: \<open>\<not> stall (flush1 (flush1 (impl_step im s)))\<close>
  shows \<open>abstract (impl_step im s) = abstract (impl_step im (flush1 (flush1 s)))\<close>
proof-
  let ?s' = \<open>impl_step im s\<close>
  let ?s'1 = \<open>flush1 ?s'\<close>
  let ?s'2 = \<open>flush1 ?s'1\<close>
  let ?s1 = \<open>flush1 s\<close>
  let ?s2 = \<open>flush1 ?s1\<close>
  let ?s2' = \<open>impl_step im ?s2\<close>
  have s1_no_stall: \<open>\<not> stall (flush1 s)\<close> using no_stall_imp_next_no_stall[OF s_no_stall] .
  have s2_no_stall: \<open>\<not> stall (flush1 (flush1 s))\<close> using no_stall_imp_next_no_stall[OF s1_no_stall] .
  have s1_de_empty: \<open>\<not> mips_de_valid ?s1\<close> using no_stall_imp_next_de_empty[OF s_no_stall] .
  have s2_de_empty: \<open>\<not> mips_de_valid ?s2\<close> using de_empty_imp_next_de_empty[OF s1_de_empty] .
  have s2'_de_valid: \<open>mips_de_valid ?s2'\<close> using de_empty_imp_next_de_valid'[OF s2_de_empty] .
  (*have wb_conv_s1_s': \<open>mips_wb ?s1 = mips_wb ?s'\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)*)
  have wb_conv_s2_s'1: \<open>mips_wb ?s2 = mips_wb ?s'1\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have rf_conv_s2_s'1: \<open>mips_rf ?s2 = mips_rf ?s'1\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have dm_conv_s2_s'1: \<open>mips_dm ?s2 = mips_dm ?s'1\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have mem_conv_s2_s'1: \<open>mips_mem ?s2 = mips_mem ?s'1\<close>
    by (simp add: flush1_def impl_step_def mips_upd_def Let_def)
  have inst_conv_s2'_s'2: \<open>mips_inst ?s2' = mips_inst ?s'2\<close>
    apply(subst impl_step_inst_conv[OF s2_de_empty])
    apply(subst stall_imp_inst_unchanged[OF s'1_stall])
    apply(subst flush1_same_pc[OF s1_de_empty])
    apply(subst flush1_same_pc2[OF s'_de_valid])
    apply(subst stall_imp_inst_unchanged[OF s'_stall])
    apply(subst impl_step_inst_conv2[OF s_no_stall])
    by (rule refl)
  have s'2_de_valid: \<open>mips_de_valid ?s'2\<close>
    by (simp add: stall_imp_next_de_valid[OF s'1_stall])
  have s2'_ex_empty: \<open>ex_empty ?s2'\<close> using de_empty_imp_next_ex_empty'[OF s2_de_empty] .
  have s'2_ex_empty: \<open>ex_empty ?s'2\<close> using stall_imp_next_ex_empty[OF s'1_stall] .
  have s2_ex_empty: \<open>ex_empty ?s2\<close> using de_empty_imp_next_ex_empty[OF s1_de_empty] .
  have s2'_mem_empty: \<open>mem_empty ?s2'\<close> using ex_empty_imp_next_mem_empty'[OF s2_ex_empty] .
  have s'1_ex_empty: \<open>ex_empty ?s'1\<close> using stall_imp_next_ex_empty[OF s'_stall] .
  have s'2_mem_empty: \<open>mem_empty ?s'2\<close> using ex_empty_imp_next_mem_empty[OF s'1_ex_empty] .
  have sim: \<open>mips_state_sim ?s'2 ?s2'\<close>
    apply(simp add: mips_state_sim_def Let_def)
    apply(rule conjI)
     apply(subst stall_pc_unchanged[OF s'1_stall])
     apply(subst stall_pc_unchanged[OF s'_stall])
    apply(subst impl_step_inc_pc[OF s_no_stall s'_de_valid])
     apply(subst impl_step_inc_pc[OF s2_no_stall s2'_de_valid])
     apply(subst flush1_same_pc[OF s1_de_empty])
     apply(subst flush1_same_pc2[OF s'_de_valid])
     apply(rule refl)
    apply(rule conjI)
     apply(subgoal_tac \<open>regfile_r (mips_rf (flush1 (flush1 (impl_step im s)))) = regfile_r (mips_rf (impl_step im (flush1 (flush1 s))))\<close>)
    apply simp
     apply(subst next_rf)
     apply(subst next_rf')
    apply(simp add: wb_conv_s2_s'1 rf_conv_s2_s'1 dm_conv_s2_s'1)
    apply(rule conjI)
     apply(subst next_dm) apply(subst next_dm')
     apply(simp add: mem_conv_s2_s'1 dm_conv_s2_s'1)
    apply(rule conjI)
    using s'2_de_valid s2'_de_valid inst_conv_s2'_s'2 apply argo
    apply(rule conjI)
    using s'2_ex_empty[simplified] s2'_ex_empty[simplified] apply metis
    apply(rule conjI)
    using s'2_mem_empty[simplified] s2'_mem_empty[simplified] apply metis
    apply(simp add: next_wb next_wb')
    apply(rule disjI2)
    apply(simp add: mem_conv_s2_s'1)
    done
  have \<open>proj (flush (flush1 (flush1 (impl_step im s)))) = proj (flush (impl_step im s))\<close>
    apply(rule sim_imp_same_proj)
    apply(rule sim_trans[of _ \<open>flush (flush1 (impl_step im s))\<close>])
    by (rule flush_flush1_sim)+
  then show ?thesis using sim_imp_same_abstract[OF sim]
    by (simp add: abstract_def)
qed

definition impl_step' where
  \<open>impl_step' im s \<equiv>
     let s' = impl_step im (run_until_no_stall s) in
     if mips_de_valid s' then s' else impl_step im s'\<close>

lemma impl_step'_de_valid:
  \<open>mips_de_valid (impl_step' im s)\<close>
  apply(auto simp add: impl_step'_def Let_def)
  by (rule de_empty_imp_next_de_valid')

lemma abstract_conv_run_until_no_stall:
  \<open>abstract s = abstract (run_until_no_stall s)\<close>
  apply(simp add: abstract_def)
  apply(auto simp add: run_until_no_stall_def Let_def)
   apply(rule sim_imp_same_proj)
   apply(rule sim_trans[of _ \<open>flush (flush1 s)\<close>])
    apply(rule sim_sym) apply(rule flush_flush1_sim)
   apply(rule sim_sym) apply(rule flush_flush1_sim)
  apply(rule sim_imp_same_proj)
  apply(rule sim_sym) apply(rule flush_flush1_sim)
  done

lemma abstract_conv_flush1:
  \<open>abstract (flush1 s) = abstract s\<close>
  apply(simp add: abstract_def)
  apply(rule sim_imp_same_proj)
  by (rule flush_flush1_sim)

lemma sim_imp_same_stall:
  \<open>mips_state_sim s1 s2 \<Longrightarrow> stall s1 = stall s2\<close>
  apply(simp add: mips_state_sim_def Let_def stall_def)
  apply(cases \<open>mips_de_valid s1\<close>; simp)
   apply(subgoal_tac \<open>ExecuteStage_rf_wa (mips_ex s1) = ExecuteStage_rf_wa (mips_ex s2)\<close>)
    prefer 2 apply(cases \<open>mips_ex s1 = mips_ex s2\<close>; simp)
   apply(subgoal_tac \<open>MemoryStage_rf_wa (mips_mem s1) = MemoryStage_rf_wa (mips_mem s2)\<close>)
    prefer 2 apply(cases \<open>mips_mem s1 = mips_mem s2\<close>; simp)
   apply simp
  apply(simp add: data_hazard_def eqnz_def)
  done

lemma exec_correct':
  \<open>\<not> stall s \<Longrightarrow> mips_de_valid (impl_step im s) \<Longrightarrow>
   mips.exec load store im (abstract s) (abstract (impl_step im s))\<close>
  apply(cases \<open>stall (impl_step im s)\<close>)
   apply(cases \<open>stall (flush1 (impl_step im s))\<close>)
    apply(subst abstract_conv_stall2) apply assumption+ apply(rule flush2_no_stall)
    apply(subst abstract_conv_flush1[of s, symmetric])
    apply(subst abstract_conv_flush1[of \<open>flush1 s\<close>, symmetric])
    apply(rule exec_correct) apply(rule flush2_no_stall)
     apply(rule de_empty_imp_next_de_valid')
     apply(rule de_empty_imp_next_de_empty)
     apply(erule no_stall_imp_next_de_empty)
    apply(rule ex_and_mem_empty_imp_no_stall)
     apply(rule de_empty_imp_next_ex_empty')
     apply(rule de_empty_imp_next_de_empty)
     apply(erule no_stall_imp_next_de_empty)
    apply(rule ex_empty_imp_next_mem_empty')
    apply(rule de_empty_imp_next_ex_empty)
    apply(erule no_stall_imp_next_de_empty)
   apply(subst abstract_conv_stall1) apply assumption+
   apply(subst abstract_conv_flush1[of s, symmetric])
   apply(rule exec_correct)
     apply(rule de_empty_imp_no_stall)
     apply(erule no_stall_imp_next_de_empty)
    apply(rule de_empty_imp_next_de_valid')
    apply(erule no_stall_imp_next_de_empty)
   apply(subgoal_tac \<open>stall (flush1 (impl_step im s)) = stall (impl_step im (flush1 s))\<close>)
    apply blast
   apply(rule sim_imp_same_stall)
   apply(rule sim_s'1_s1') apply assumption+
  apply(rule exec_correct) apply assumption+
  done

theorem mips_correct:
  \<open>mips.exec load store im (abstract s) (abstract (impl_step' im s))\<close>
  apply(cases \<open>mips_de_valid (impl_step im s)\<close>; simp add: impl_step'_def Let_def)
   apply(cases \<open>stall s\<close>)
    apply auto[1]
     apply(subst abstract_conv_run_until_no_stall[of s])
     apply(rule exec_correct') apply(rule run_until_no_stall_correct) apply assumption+
    apply(subst abstract_conv_run_until_no_stall[of s])
    apply(subst exec_correct_kill[of \<open>impl_step im (run_until_no_stall s)\<close> im])
       apply(rule refl) apply(rule run_until_no_stall_correct) apply assumption
    apply(rule exec_correct')
     apply(erule de_empty_imp_no_stall)
    apply(erule de_empty_imp_next_de_valid')
   apply auto[1]
    apply(subst run_until_no_stall_same) apply assumption
  using exec_correct' apply blast
   apply(subst run_until_no_stall_same) apply assumption
   apply(subst (asm) run_until_no_stall_same) apply assumption apply blast
  apply auto[1]
   apply(subst abstract_conv_run_until_no_stall)
   apply(rule exec_correct')
    apply(rule run_until_no_stall_correct)
   apply assumption
  apply(subst abstract_conv_run_until_no_stall)
  apply(subst exec_correct_kill[of \<open>impl_step im (run_until_no_stall s)\<close> im])
     apply(rule refl) apply(rule run_until_no_stall_correct) apply assumption
  apply(rule exec_correct')
   apply(erule de_empty_imp_no_stall)
  apply(erule de_empty_imp_next_de_valid')
  done

end
