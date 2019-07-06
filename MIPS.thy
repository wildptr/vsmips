theory MIPS
  imports Word_Lib.Word_Lib
begin

type_synonym reg = \<open>5 word\<close>
type_synonym w = \<open>32 word\<close>
type_synonym imm = \<open>16 word\<close>
type_synonym J_operand = \<open>26 word\<close>
type_synonym shamt = \<open>5 word\<close>
type_synonym byte = \<open>8 word\<close>
type_synonym pc = \<open>30 word\<close>

datatype ALU_op =
  OP_ADD | OP_SUB | OP_AND | OP_OR | OP_XOR | OP_NOR |
  OP_SLT | OP_SLTU

primrec is_bitwise_op where
  \<open>is_bitwise_op OP_ADD  = False\<close> |
  \<open>is_bitwise_op OP_SUB  = False\<close> |
  \<open>is_bitwise_op OP_AND  = True \<close> |
  \<open>is_bitwise_op OP_OR   = True \<close> |
  \<open>is_bitwise_op OP_XOR  = True \<close> |
  \<open>is_bitwise_op OP_NOR  = True \<close> |
  \<open>is_bitwise_op OP_SLT  = False\<close> |
  \<open>is_bitwise_op OP_SLTU = False\<close>

datatype shift_op =
  OP_SLL | OP_SRL | OP_SRA

datatype br_pred2 = EQ | NE
datatype br_pred1 = LEZ | GTZ

primrec ALU_op_fn :: \<open>ALU_op \<Rightarrow> w \<Rightarrow> w \<Rightarrow> w\<close> where
  \<open>ALU_op_fn OP_ADD = (+)\<close> |
  \<open>ALU_op_fn OP_SUB = (-)\<close> |
  \<open>ALU_op_fn OP_AND = (AND)\<close> |
  \<open>ALU_op_fn OP_OR = (OR)\<close> |
  \<open>ALU_op_fn OP_XOR = (XOR)\<close> |
  \<open>ALU_op_fn OP_NOR a b = NOT (a OR b)\<close> |
  \<open>ALU_op_fn OP_SLT  a b = (if a <s b then 1 else 0)\<close> |
  \<open>ALU_op_fn OP_SLTU a b = (if a < b then 1 else 0)\<close>

primrec shift_op_fn :: \<open>shift_op \<Rightarrow> w \<Rightarrow> 5 word \<Rightarrow> w\<close> where
  \<open>shift_op_fn OP_SLL a b = a <<  unat b\<close> |
  \<open>shift_op_fn OP_SRL a b = a >>  unat b\<close> |
  \<open>shift_op_fn OP_SRA a b = a >>> unat b\<close>

datatype mem_req_size = BYTE | HALF | WORD

datatype inst =
  Inst_ALU_R ALU_op reg reg reg | (* op  rd, rs, rt *)
  Inst_ALU_I ALU_op reg reg imm | (* op  rt, rs, imm *)
  Inst_Shift_R shift_op reg reg reg | (* op  rd, rt, rs *)
  Inst_Shift_I shift_op reg reg shamt | (* op  rd, rt, shamt *)
  Inst_LUI reg imm | (* LUI  rt, imm *)
  Inst_J J_operand |
  Inst_JAL J_operand |
  Inst_JR reg | (* JR  rs *)
  Inst_JALR reg reg | (* JALR  rd, rs *)
  Inst_Branch br_pred2 reg reg imm | (* op  rs, rt, imm *)
  Inst_Branch1 br_pred1 reg imm | (* op  rs, imm *)
  Inst_Load mem_req_size bool reg reg imm |
  Inst_Store mem_req_size reg reg imm |
  Inst_Undef

primrec br_pred2_fn :: \<open>br_pred2 \<Rightarrow> w \<Rightarrow> w \<Rightarrow> bool\<close> where
  \<open>br_pred2_fn EQ = (=)\<close> |
  \<open>br_pred2_fn NE = (\<noteq>)\<close>

primrec br_pred1_fn :: \<open>br_pred1 \<Rightarrow> w \<Rightarrow> bool\<close> where
  \<open>br_pred1_fn LEZ = (\<lambda>a. sint a \<le> 0)\<close> |
  \<open>br_pred1_fn GTZ = (\<lambda>a. sint a > 0)\<close>

type_synonym regfile = \<open>reg \<Rightarrow> w\<close>

record 'm isa_state =
  PC :: pc
  Regs :: regfile
  Mem :: 'm

definition read_rf :: \<open>reg \<Rightarrow> regfile \<Rightarrow> w\<close> where
  \<open>read_rf a rf \<equiv> if a = 0 then 0 else rf a\<close>

definition write_rf :: \<open>reg \<Rightarrow> w \<Rightarrow> regfile \<Rightarrow> regfile\<close> where
  \<open>write_rf a d rf \<equiv> if a = 0 then rf else rf(a:=d)\<close>

type_synonym imem = \<open>pc \<Rightarrow> w\<close>

locale mips = 
  fixes load :: "32 word \<Rightarrow> mem_req_size \<Rightarrow> 'm \<Rightarrow> 32 word"
  fixes store :: "32 word \<Rightarrow> mem_req_size \<Rightarrow> 32 word \<Rightarrow> 'm \<Rightarrow> 'm"

begin

definition load_ext :: \<open>w \<Rightarrow> mem_req_size \<Rightarrow> bool \<Rightarrow> 'm \<Rightarrow> w\<close> where
  \<open>load_ext addr sz sign m \<equiv>
     let data = load addr sz m in
     case sz of
       BYTE \<Rightarrow>
         if sign then (scast (ucast data ::  8 word) :: w)
                 else (ucast (ucast data ::  8 word) :: w) |
       HALF \<Rightarrow>
         if sign then (scast (ucast data :: 16 word) :: w)
                 else (ucast (ucast data :: 16 word) :: w) |
       WORD \<Rightarrow> data\<close>

(*
definition align4 :: \<open>w \<Rightarrow> w\<close> where
  \<open>align4 addr = addr AND -4\<close>
*)

(*
definition load_byte :: \<open>memory \<Rightarrow> w \<Rightarrow> w\<close> where
  \<open>load_byte m addr = ucast (m addr)\<close>

definition load_word :: \<open>memory \<Rightarrow> w \<Rightarrow> w\<close> where
  \<open>load_word m addr \<equiv> word_rcat
   [m (align addr OR 3),
    m (align addr OR 2),
    m (align addr OR 1),
    m (align addr     )]\<close>

definition store_byte :: \<open>memory \<Rightarrow> w \<Rightarrow> w \<Rightarrow> memory\<close> where
  \<open>store_byte m addr data \<equiv> m(addr := ucast data)\<close>

definition store_word :: \<open>memory \<Rightarrow> w \<Rightarrow> w \<Rightarrow> memory\<close> where
  \<open>store_word m addr data \<equiv>
   m(align addr      := ucast (data      ),
     align addr OR 1 := ucast (data >>  8),
     align addr OR 2 := ucast (data >> 16),
     align addr OR 3 := ucast (data >> 24))\<close>
*)

definition sext :: \<open>imm \<Rightarrow> w\<close> where \<open>sext = scast\<close>

definition jump_dest :: \<open>pc \<Rightarrow> J_operand \<Rightarrow> pc\<close> where
  \<open>jump_dest pc imm \<equiv> word_cat (slice 26 (pc + 1) :: 4 word) imm\<close>

definition ret_addr :: \<open>pc \<Rightarrow> w\<close> where
  \<open>ret_addr pc = word_cat (pc+2) (0::2 word)\<close>

inductive isa_step :: \<open>'m isa_state \<Rightarrow> inst \<Rightarrow> 'm isa_state \<Rightarrow> bool\<close> ("_ \<midarrow>_\<rightarrow> _" [81,0,81] 80) where
ALU_R:
  \<open>t = s\<lparr>PC := PC s + 1, Regs := write_rf rd (ALU_op_fn op (read_rf rs (Regs s)) (read_rf rt (Regs s))) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_ALU_R op rd rs rt\<rightarrow> t\<close> |
ALU_I:
  \<open>t = s\<lparr>PC := PC s + 1, Regs := write_rf rt (ALU_op_fn op (read_rf rs (Regs s)) (if is_bitwise_op op then ucast imm else scast imm)) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_ALU_I op rt rs imm\<rightarrow> t\<close> |
Shift_R:
  \<open>t = s\<lparr>PC := PC s + 1, Regs := write_rf rd (shift_op_fn op (read_rf rt (Regs s)) (ucast (read_rf rs (Regs s)))) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Shift_R op rd rt rs\<rightarrow> t\<close> |
Shift_I:
  \<open>t = s\<lparr>PC := PC s + 1, Regs := write_rf rd (shift_op_fn op (read_rf rt (Regs s)) shamt) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Shift_I op rd rt shamt\<rightarrow> t\<close> |
LUI:
  \<open>t = s\<lparr>PC := PC s + 1, Regs := write_rf rt (word_cat imm (0::16 word)) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_LUI rt imm\<rightarrow> t\<close> |
J:
  \<open>t = s\<lparr>PC := jump_dest (PC s) imm\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_J imm\<rightarrow> t\<close> |
JAL:
  \<open>t = s\<lparr>PC := jump_dest (PC s) imm, Regs := write_rf 31 (ret_addr (PC s)) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_JAL imm\<rightarrow> t\<close> |
JR:
  \<open>t = s\<lparr>PC := slice 2 (read_rf rs (Regs s))\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_JR rs\<rightarrow> t\<close> |
JALR:
  \<open>t = s\<lparr>PC := slice 2 (read_rf rs (Regs s)), Regs := write_rf rd (ret_addr (PC s)) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_JALR rd rs\<rightarrow> t\<close> |
Branch_taken:
  \<open>br_pred2_fn pred (read_rf rs (Regs s)) (read_rf rt (Regs s)) \<Longrightarrow>
   t = s\<lparr>PC := PC s + 1 + scast imm\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Branch pred rs rt imm\<rightarrow> t\<close> |
Branch_not_taken:
  \<open>\<not> br_pred2_fn pred (read_rf rs (Regs s)) (read_rf rt (Regs s)) \<Longrightarrow>
   t = s\<lparr>PC := PC s + 1\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Branch pred rs rt imm\<rightarrow> t\<close> |
Branch1_taken:
  \<open>br_pred1_fn pred (read_rf rs (Regs s)) \<Longrightarrow>
   t = s\<lparr>PC := PC s + 1 + scast imm\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Branch1 pred rs imm\<rightarrow> t\<close> |
Branch1_not_taken:
  \<open>\<not> br_pred1_fn pred (read_rf rs (Regs s)) \<Longrightarrow>
   t = s\<lparr>PC := PC s + 1\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Branch1 pred rs imm\<rightarrow> t\<close> |
Load:
  \<open>t = s\<lparr>PC := PC s + 1, Regs := write_rf rt (load_ext (read_rf rs (Regs s) + sext imm) sz sign (Mem s)) (Regs s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Load sz sign rt rs imm\<rightarrow> t\<close> |
Store:
  \<open>t = s\<lparr>PC := PC s + 1, Mem := store (read_rf rs (Regs s) + sext imm) sz (read_rf rt (Regs s)) (Mem s)\<rparr> \<Longrightarrow>
   s \<midarrow>Inst_Store sz rt rs imm\<rightarrow> t\<close> |
Undef:
  \<open>s \<midarrow>Inst_Undef\<rightarrow> t\<close>

definition decode :: \<open>w \<Rightarrow> inst\<close> where
  \<open>decode inst \<equiv>
     let opcode = slice 26 inst :: 6 word in
     if opcode = 0 then
       case (slice 21 inst :: 5 word, slice 16 inst :: 5 word, slice 11 inst, slice 6 inst :: 5 word, ucast inst :: 6 word) of (rs, rt, rd, shamt, funct) \<Rightarrow>
       if funct =  0 then Inst_Shift_I OP_SLL rd rt shamt else
       if funct =  2 then Inst_Shift_I OP_SRL rd rt shamt else
       if funct =  3 then Inst_Shift_I OP_SRA rd rt shamt else
       if funct =  4 then Inst_Shift_R OP_SLL rd rt rs else
       if funct =  6 then Inst_Shift_R OP_SRL rd rt rs else
       if funct =  7 then Inst_Shift_R OP_SRA rd rt rs else
       if funct =  8 then Inst_JR rs else
       if funct =  9 then Inst_JALR rd rs else
\<comment> \<open>a number of instructions omitted here\<close>
       if funct = 32 then Inst_ALU_R OP_ADD  rd rs rt else
       if funct = 33 then Inst_ALU_R OP_ADD  rd rs rt else \<comment> \<open>exceptions not supported for now\<close>
       if funct = 34 then Inst_ALU_R OP_SUB  rd rs rt else
       if funct = 35 then Inst_ALU_R OP_SUB  rd rs rt else
       if funct = 36 then Inst_ALU_R OP_AND  rd rs rt else
       if funct = 37 then Inst_ALU_R OP_OR   rd rs rt else
       if funct = 38 then Inst_ALU_R OP_XOR  rd rs rt else
       if funct = 39 then Inst_ALU_R OP_NOR  rd rs rt else
       if funct = 42 then Inst_ALU_R OP_SLT  rd rs rt else
       if funct = 43 then Inst_ALU_R OP_SLTU rd rs rt else
       Inst_Undef
    else
    if opcode = 2 then let imm = ucast inst :: J_operand in Inst_J imm else
    if opcode = 3 then let imm = ucast inst :: J_operand in Inst_JAL imm else
    case (slice 21 inst :: 5 word, slice 16 inst :: 5 word, ucast inst :: 16 word) of (rs, rt, imm) \<Rightarrow>
    if opcode =  4 then Inst_Branch EQ rs rt imm else \<comment> \<open>BEQ\<close>
    if opcode =  5 then Inst_Branch NE rs rt imm else \<comment> \<open>BNE\<close>
    if opcode =  6 then Inst_Branch1 LEZ rs imm else \<comment> \<open>BLEZ\<close>
    if opcode =  7 then Inst_Branch1 GTZ rs imm else \<comment> \<open>BGTZ\<close>
    if opcode =  8 then Inst_ALU_I OP_ADD  rt rs imm else
    if opcode =  9 then Inst_ALU_I OP_ADD  rt rs imm else \<comment> \<open>ADDU\<close>
    if opcode = 10 then Inst_ALU_I OP_SLT  rt rs imm else
    if opcode = 11 then Inst_ALU_I OP_SLTU rt rs imm else
    if opcode = 12 then Inst_ALU_I OP_AND  rt rs imm else
    if opcode = 13 then Inst_ALU_I OP_OR   rt rs imm else
    if opcode = 14 then Inst_ALU_I OP_XOR  rt rs imm else
    if opcode = 15 then Inst_LUI rt imm else
    if opcode = 32 then Inst_Load BYTE True  rt rs imm else \<comment> \<open>LB\<close>
    if opcode = 33 then Inst_Load HALF True  rt rs imm else \<comment> \<open>LH\<close>
    if opcode = 34 then Inst_Load WORD False rt rs imm else \<comment> \<open>LW\<close>
    if opcode = 36 then Inst_Load BYTE False rt rs imm else \<comment> \<open>LBU\<close>
    if opcode = 37 then Inst_Load HALF False rt rs imm else \<comment> \<open>LHU\<close>
    if opcode = 40 then Inst_Store BYTE rt rs imm else \<comment> \<open>SB\<close>
    if opcode = 41 then Inst_Store HALF rt rs imm else \<comment> \<open>SH\<close>
    if opcode = 43 then Inst_Store WORD rt rs imm else \<comment> \<open>SW\<close>
    Inst_Undef\<close>

(*
inductive (* exec im init n fin *) exec :: \<open>imem \<Rightarrow> 'm isa_state \<Rightarrow> nat \<Rightarrow> 'm isa_state \<Rightarrow> bool\<close>
  for im :: imem
  where
    exec0:
    \<open>exec im s 0 s\<close> |
    execS:
    \<open>step s (decode (im (PC s))) s' \<Longrightarrow> exec im s' n t \<Longrightarrow> exec im s (Suc n) t\<close>
*)

definition \<open>exec im s t \<equiv> s \<midarrow>decode (im (PC s))\<rightarrow> t\<close>

(*
lemma \<open>s \<midarrow>decode 0\<rightarrow> t \<Longrightarrow> t = s\<lparr>PC := PC s + 1\<rparr>\<close>
  apply(simp add: decode_def)
  apply(erule isa_step.cases, auto)
  apply(simp add: write_rf_def read_rf_def)
  done
*)

end (* locale *)

end (* theory *)
