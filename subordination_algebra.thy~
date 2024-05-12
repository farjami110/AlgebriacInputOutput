theory subordination_algebra
  imports boolean_algebra_infinitary

begin

declare[[show_types=false]] (*switch this on/off to see the actual types (useful to debug polymorphism problems)*)

(*Input/output rules*)
(*David: it is better to always give an explicit type to each definition (to avoid polymorphic confusions ;) *)
definition SI::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>SI \<rho> \<equiv> \<forall>a b x. \<rho> b x \<and> (a \<^bold>\<preceq> b)\<longrightarrow> \<rho> a x\<close> 
definition WO::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>WO \<rho> \<equiv> \<forall>a x y. \<rho> a x \<and> (x \<^bold>\<preceq> y)\<longrightarrow> \<rho> a y\<close> 
definition AND::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>AND \<rho> \<equiv> \<forall>a x y. \<rho> a x \<and> \<rho> a y \<longrightarrow> \<rho> a (x\<^bold>\<and>y)\<close> 
definition OR::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>OR \<rho> \<equiv> \<forall>a b x. \<rho> a x \<and> \<rho> b x \<longrightarrow> \<rho> (a\<^bold>\<or>b) x\<close> 
definition CT::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>CT \<rho> \<equiv> \<forall>a x y. \<rho> a x \<and> \<rho> (a\<^bold>\<and>x) y \<longrightarrow> \<rho> a y\<close> 
definition Top::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Top \<rho> \<equiv> \<rho> \<^bold>\<top> \<^bold>\<top>\<close>


(*New rules*)
definition Bot::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Bot \<rho> \<equiv> \<rho> \<^bold>\<bottom> \<^bold>\<bottom>\<close>
definition T::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where  \<open>T \<rho> \<equiv> \<forall>a x y. \<rho> a x \<and> \<rho> x y  \<longrightarrow> \<rho> a y\<close> 
definition D::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>D \<rho> \<equiv> \<forall>a c. \<rho> a c \<longrightarrow> (\<exists>b. (\<rho> a b) \<and> (\<rho> b c))\<close> 
definition S6::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>S6 \<rho> \<equiv> \<forall>a b. \<rho> a b \<longrightarrow> \<rho>(\<^bold>\<midarrow>b)(\<^bold>\<midarrow>a)\<close> 
definition DD::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>DD \<rho> \<equiv> \<forall>a x\<^sub>1 x\<^sub>2. \<rho> a x\<^sub>1 \<and> \<rho> a x\<^sub>2 \<longrightarrow> (\<exists>x. \<rho> a x \<and> (x \<^bold>\<preceq> x\<^sub>1) \<and> (x \<^bold>\<preceq> x\<^sub>2))\<close>
definition UD::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool"  where \<open>UD \<rho> \<equiv> \<forall> a\<^sub>1 a\<^sub>2 x. \<rho> a\<^sub>1 x \<and> \<rho> a\<^sub>2 x \<longrightarrow> (\<exists>a. \<rho> a x \<and> (a\<^sub>1 \<^bold>\<preceq> a) \<and> (a\<^sub>2 \<^bold>\<preceq> a))\<close> 
definition SF::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>SF \<rho> \<equiv> \<forall>x. \<exists>y. \<rho> x y  \<close> 
definition SB::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool"  where \<open>SB \<rho> \<equiv> \<forall>x. \<exists>y. \<rho> y x  \<close>

named_theorems IO_def (* Input/output rules definitions *)
declare AND_def[IO_def] DD_def [IO_def]  SI_def[IO_def] WO_def[IO_def] OR_def[IO_def] CT_def[IO_def] Top_def[IO_def]
Bot_def[IO_def] T_def[IO_def] D_def[IO_def] S6_def[IO_def] UD_def[IO_def]

(*WO and SI are encoded right*)
lemma "(SI \<rho>) \<and> (WO \<rho>) \<and> (\<exists>h g. \<rho> h g) " nitpick[satisfy,show_all,card 'a=1] oops
lemma "\<^bold>\<bottom>  \<^bold>\<preceq> \<^bold>\<top>"  by (simp add: subset_def top_def)
lemma "\<^bold>\<bottom>  \<^bold>\<preceq> X"  by (simp add: bottom_def subset_def)

(*Lemma 3.2*)
lemma AND_DD: "AND \<rho>  \<longrightarrow> DD \<rho>" unfolding AND_def and DD_def by (metis L3 L4 L5)
lemma OR_UD: "OR \<rho> \<longrightarrow> UD \<rho>"   unfolding OR_def and UD_def by (metis join_def subset_def)
lemma SI_UD_OR: "SI \<rho> \<longrightarrow> (UD \<rho> \<longrightarrow> OR \<rho>)" unfolding SI_def and UD_def and OR_def by (meson L7)
lemma WO_DD_AND: "WO \<rho> \<longrightarrow> (DD \<rho> \<longrightarrow> AND \<rho>)" unfolding WO_def and DD_def and AND_def by (meson L8)  

(*Lemma 3.3*)
lemma SISF: "SI \<rho> \<longrightarrow> (Top \<rho> \<longrightarrow> SF \<rho>)"  by (metis (mono_tags, opaque_lifting) SF_def SI_def Top_def subset_def top_def)
lemma SISB: "SI \<rho> \<longrightarrow> (SB \<rho> \<longrightarrow> Bot \<rho>)" by (metis Bot_def L14 L4 L5 SB_def SI_def)
lemma WOSB: "WO \<rho> \<longrightarrow> (Bot \<rho> \<longrightarrow> SB \<rho>)"  by (metis (mono_tags, opaque_lifting) Bot_def SB_def WO_def bottom_def subset_def)
lemma WOSF: "WO \<rho> \<longrightarrow> (SF \<rho> \<longrightarrow> Top \<rho>)" by (metis (mono_tags, opaque_lifting) SF_def Top_def WO_def subset_def top_def)

definition "up_directed S \<equiv> \<forall>X Y. (S X \<and> S Y) \<longrightarrow> (\<exists>Z. S Z \<and> X \<^bold>\<preceq> Z \<and> Y \<^bold>\<preceq> Z)"
definition "down_directed S \<equiv> \<forall>X Y. (S X \<and> S Y) \<longrightarrow> (\<exists>Z. S Z \<and> X \<^bold>\<succeq> Z \<and> Y \<^bold>\<succeq> Z)"

(*David: verified some (maybe useful?) properties*)
lemma aux1: "DD \<rho> \<Longrightarrow> down_directed (\<lambda>x. \<rho> a x)" by (simp add: DD_def down_directed_def)
lemma aux2: "UD \<rho> \<Longrightarrow> up_directed (\<lambda>x. \<rho> x a)" by (simp add: UD_def up_directed_def)

definition "filter_boolean S \<equiv> down_directed S \<and> upwards_closed S"
definition "ideal_boolean S \<equiv> up_directed S \<and> downwards_closed S"

(*Defining subordination relation*)
definition subordination_def: "subordination \<rho> \<equiv> SI \<rho> \<and> WO \<rho> \<and> AND \<rho> \<and> OR \<rho> \<and> Bot \<rho> \<and> Top \<rho> \<and> SF \<rho> \<and> SB \<rho>"

(*The image of a subordination relation is filter and the inverse image an ideal*)
lemma imag_filter: "\<forall>x. subordination \<rho> \<longrightarrow>  filter_boolean  (\<lambda>y. \<rho> x y)" unfolding subordination_def  
  by (smt (verit, ccfv_SIG) AND_DD DD_def WO_def down_directed_def filter_boolean_def upwards_closed_def)

lemma invers_ideal: "\<forall>x. subordination \<rho> \<longrightarrow>  ideal_boolean  (\<lambda>y. \<rho> y x)" 
  unfolding subordination_def downwards_closed_def ideal_boolean_def up_directed_def
  by (metis OR_UD SI_def UD_def)


(*Working on definition 2.5*)
(*David: I see you want to encode arbitrary BAs as subalgebras of the power-set algebra that is based on the
type's domain (i.e. 'w). I am not sure this works for your purposes. Anyhow, I would simplify definitions a bit*)
(*Required definitions (?)*)
(* definition "boolean_algebra S \<equiv> \<forall>X Y. (S X \<and> S Y) \<longrightarrow> (S (X \<^bold>\<and> Y) \<and> S (X \<^bold>\<or> Y) \<and> S (\<^bold>\<midarrow>X) \<and> S \<^bold>\<top> \<and> S \<^bold>\<bottom>)" *)
definition "complement_closed S \<equiv> (\<forall>X. S X \<longrightarrow> S (\<^bold>\<midarrow>X))"
definition "boolean_algebra S \<equiv> meet_closed S \<and> S \<^bold>\<bottom> \<and> complement_closed S"
lemma boolean_algebra_def2: "boolean_algebra S = (join_closed S \<and> S \<^bold>\<top> \<and> complement_closed S)"
  by (smt (z3) BA_deMorgan1 BA_distr2 BA_dn L13 L14 L5 boolean_algebra_def complement_closed_def join_closed_def meet_closed_def)

definition "complete_boolean_algebra S \<equiv>  infimum_closed S \<and> complement_closed S"
lemma complete_boolean_algebra_def2: "complete_boolean_algebra S = (supremum_closed S \<and> complement_closed S)"
  unfolding complement_closed_def by (smt (verit) BA_dn complement_closed_def complete_boolean_algebra_def dom_compl_def iDM_a iDM_b infimum_closed_def setequ_equ supremum_closed_def)

lemma completeBAprop: "complete_boolean_algebra S \<longrightarrow> boolean_algebra S" 
  by (metis boolean_algebra_def complete_boolean_algebra_def complete_boolean_algebra_def2 inf_closed_char inf_meet_closed sup_closed_char)

(*David: do not confuse  \<^bold>\<preceq> with \<sqsubseteq> *)
definition "sub_boolean_algebra S V \<equiv> boolean_algebra S \<and> boolean_algebra V \<and> S \<sqsubseteq> V" 

(* definition "complete S \<equiv> infimum_closed' S \<and> supremum_closed' S" *)

 
definition "closed cl A B \<equiv> A cl \<and> (\<exists> F. F \<sqsubseteq> B \<and> down_directed F \<and> (cl \<^bold>\<approx> \<^bold>\<And>F))" 
definition "open  op A B \<equiv> A op \<and> (\<exists> I. I \<sqsubseteq> B \<and> up_directed I \<and> (op \<^bold>\<approx> \<^bold>\<Or>I))"

(*David: here you might also want to keep definitions clean by assuming preconditions (Boolean (sub-)algebra) *)
definition "denseIn B A \<equiv> \<forall>X. A X \<longrightarrow> (\<exists>F.  (F \<sqsubseteq> B) \<and> (\<forall>Y. F Y \<longrightarrow> closed Y A B) \<and> (X \<^bold>\<approx> \<^bold>\<And>F) ) \<and>
 (\<exists>E.  (E \<sqsubseteq> B) \<and> (\<forall>Y. E Y \<longrightarrow> open Y A B) \<and> (X \<^bold>\<approx> \<^bold>\<Or>E) )" (*David: rename maybe? read as B is dense in A *)
definition "compactIn B A \<equiv> \<forall>F I. nonEmpty F \<and> nonEmpty I \<and> (F \<sqsubseteq> B) \<and> (I \<sqsubseteq> B) \<and> down_directed F \<and> up_directed I \<longrightarrow>
  ( \<^bold>\<And>F \<^bold>\<preceq> \<^bold>\<Or> I \<longrightarrow> (\<exists>a b. F a \<and> I b \<and> a \<^bold>\<preceq> b) )"

(*the canonical extension of a boolean_algebra exists*)
lemma "\<forall>B. boolean_algebra B \<longrightarrow> (\<exists>A. complete_boolean_algebra A \<and> sub_boolean_algebra B A \<and> denseIn B A \<and> compactIn B A)"  
  (*nitpick*) oops 
(*David: sledgehammer magic doesn't work out-of-the-box, but at least now don't get countermodels, so maybe the
problem was in the (now corrected?) definition of compactness (or the encoding approach has its limitations?).
Anyhow, I wouldn't expect to prove this fully automatically, since it involves constructing a (non-trivial) witness *)

definition "Extension B A \<equiv> complete_boolean_algebra A \<and> sub_boolean_algebra B A \<and> denseIn B A \<and> compactIn B A"

(*Proposition 2.6*)
lemma Prop261iA: "((closed cl1 A B) \<and> (closed cl2 A B))\<longrightarrow> (cl1 \<sqsubseteq> cl2)  \<longrightarrow> (\<forall> b. (B b \<longrightarrow> (cl2 \<sqsubseteq> b) \<longrightarrow> (cl1 \<sqsubseteq> b)))"  
  by simp
lemma Prop261iB: "((closed cl1 A B) \<and> (closed cl2 A B)) \<longrightarrow> (\<forall> b. (B b \<longrightarrow> (cl2 \<sqsubseteq> b) \<longrightarrow> (cl1 \<sqsubseteq> b))) \<longrightarrow>  (cl1 \<sqsubseteq> cl2)" 
  by (smt (verit) closed_def infimum_def setequ_equ)
lemma Prop261iiA: "((open op1 A B) \<and> (open op2 A B))\<longrightarrow> (op1 \<sqsubseteq> op2)  \<longrightarrow> (\<forall> b. (B b \<longrightarrow> (b \<sqsubseteq> op1) \<longrightarrow> (b  \<sqsubseteq> op2)))"  
  by simp
lemma Prop261iiB: "((open op1 A B) \<and> (open op2 A B)) \<longrightarrow> (\<forall> b. (B b \<longrightarrow> (b \<sqsubseteq> op1) \<longrightarrow> (b \<sqsubseteq> op2))) \<longrightarrow>  (op1 \<sqsubseteq> op2)"
  by (smt (verit) open_def setequ_equ supremum_def)
lemma Prop261iiiA1: "((A a1) \<and> (A a2) \<and> (closed cl A B)) \<longrightarrow> (a1 \<sqsubseteq> a2) \<longrightarrow> (cl \<sqsubseteq> a1 \<longrightarrow> cl \<sqsubseteq> a2)" 
  by auto
lemma Prop261iiiB1: "((A a1) \<and> (A a2)) \<longrightarrow> (\<forall> cl. (closed cl A B)\<and> (cl \<sqsubseteq> a1 \<longrightarrow> cl \<sqsubseteq> a2)) \<longrightarrow> (a1 \<sqsubseteq> a2)"
  by blast
lemma Prop261iiiA2: "((A a1) \<and> (A a2) \<and> (open op A B)) \<longrightarrow> (a1 \<sqsubseteq> a2) \<longrightarrow> (a2 \<sqsubseteq> op \<longrightarrow> a1 \<sqsubseteq> op)" 
  by simp
lemma Prop261iiiB2: "((A a1) \<and> (A a2)) \<longrightarrow> (\<forall> op. (open op A B)\<and> (a2 \<sqsubseteq> op \<longrightarrow> a1 \<sqsubseteq> op)) \<longrightarrow> (a1 \<sqsubseteq> a2)"  
  by auto
lemma Prop26iv: "\<forall> cl1 cl2. (join_closed A \<and> sub_boolean_algebra A B \<and> (closed cl1 A B) \<and> (closed cl2 A B)) 
\<longrightarrow> (closed (cl1 \<^bold>\<or> cl2) A B)"  oops (*it needs to be formulated*)
lemma Prop26v: "\<forall> op1 op2. (meet_closed A \<and> sub_boolean_algebra A B \<and> (open op1 A B) \<and> (open op2 A B)) 
\<longrightarrow> (open (op1 \<^bold>\<and> op2) A B)" oops (*it needs to be formulated*)


(*Proposition 2.7 *)
lemma Prop271i: "( (meet_closed A) \<and> (sub_boolean_algebra D1 A) \<and> (sub_boolean_algebra D2 A) \<and> ((\<exists>x. D1 x) \<and> down_directed D1) \<and> ((\<exists>y. D2 y) \<and> down_directed D2) ) 
\<longrightarrow> (down_directed (\<lambda>x. D1 x \<and> D2 x) ) " 
  by (smt (verit, del_insts) L14 L4 L5 boolean_algebra_def down_directed_def sub_boolean_algebra_def)
(* I want to prove it for Di \<sqsubseteq> A *)

lemma Prop271ii: "((complete_boolean_algebra A \<and> sub_boolean_algebra B A \<and> closed cl1 A B \<and> closed cl2 A B) \<and>
 ((D1 \<sqsubseteq> B) \<and> (D2 \<sqsubseteq> B)\<and> (down_directed D1)\<and> (down_directed D2))\<longrightarrow> ((cl1 \<^bold>\<approx> \<^bold>\<And>D1) \<and> (cl2 \<^bold>\<approx> \<^bold>\<And>D2))\<longrightarrow> (closed (cl1 \<^bold>\<and> cl2) A B))"  
  unfolding complete_boolean_algebra_def sub_boolean_algebra_def down_directed_def closed_def oops  (*needs to try more*)

lemma Prop271iii: "( (complete_boolean_algebra A \<and> sub_boolean_algebra B A \<and> closed cl1 A B \<and> closed cl2 A B \<and> B b )\<longrightarrow>
( ((cl1\<^bold>\<and>cl2) \<^bold>\<preceq> b) \<longrightarrow> (\<exists> a1 a2. ((B a1 \<and> B a2) \<and> ((a1 \<^bold>\<and> a2) \<^bold>\<preceq> b)\<and> (cl1 \<^bold>\<preceq> a1) \<and> (cl2 \<^bold>\<preceq> a2))  ) ) )" oops
  
lemma Prop271iv: "( (complete_boolean_algebra A \<and> sub_boolean_algebra B A \<and> closed cl1 A B \<and> closed cl2 A B \<and> open op A B )\<longrightarrow>
( ((cl1\<^bold>\<and>cl2) \<^bold>\<preceq> op) \<longrightarrow> (\<exists> a1 a2 b. ((B a1 \<and> B a2 \<and> B b) \<and> ((a1 \<^bold>\<and> a2) \<^bold>\<preceq> b)\<and> (cl1 \<^bold>\<preceq> a1) \<and> (cl2 \<^bold>\<preceq> a2) \<and> (b \<^bold>\<preceq> op ) )  ) ) )" oops
  
lemma Prop272ia: "( ((Extension B A) \<and> (U1 \<sqsubseteq> B) \<and> (U2 \<sqsubseteq> B) \<and> (nonEmpty U1 ) \<and> up_directed U1) \<and> ((nonEmpty U2 ) \<and> up_directed U2) )
\<longrightarrow> (up_directed (\<lambda>x. U1 x \<or> U2 x) ) "  oops (* We need to encode the extension of set A for this theorem or use the following formulation*)

lemma Prop272ib: "( (join_closed A) \<and> (sub_boolean_algebra U1 A) \<and> (sub_boolean_algebra U2 A) \<and> ((\<exists>x. U1 x) \<and> up_directed U1) \<and> ((\<exists>y. U2 y) \<and> up_directed U2) ) 
\<longrightarrow> (up_directed (\<lambda>x. U1 x \<or> U2 x) ) "  by (metis (no_types, lifting) L13 L3 L5 boolean_algebra_def2 sub_boolean_algebra_def up_directed_def)
   
lemma Prop272ii: "((Extension B A \<and> open op1 A B \<and> open op2 A B) \<and>
 ((U1 \<sqsubseteq> B) \<and> (U2 \<sqsubseteq> B)\<and> (up_directed U1)\<and> (up_directed U2))\<longrightarrow> ((op1 \<^bold>\<approx> \<^bold>\<Or>U1) \<and> (op2 \<^bold>\<approx> \<^bold>\<Or>U2))\<longrightarrow> (open (op1 \<^bold>\<or> op2) A B))"  oops

lemma Prop272iii:  "( (Extension B A \<and> open op1 A B \<and> open op2 A B \<and> B a )\<longrightarrow>
( (a \<^bold>\<preceq> (op1 \<^bold>\<or> op2 )) \<longrightarrow> (\<exists> b1 b2. ((B b1 \<and> B b2) \<and> (a \<^bold>\<preceq> (b1 \<^bold>\<or> b2))\<and> (b1 \<^bold>\<preceq> op1) \<and> (b2 \<^bold>\<preceq> op2))  ) ) )"
  unfolding Extension_def open_def compactIn_def denseIn_def oops




 

 
end 

(*
(*Subordination relation as constant*)
consts sub :: "('w \<sigma>,'w \<sigma>)\<rho>" (infixr "\<prec>" 60)
(*Maybe we should be explicit for \<prec> on boolean_algebra *)
consts ar_Bool_al:: "'w \<sigma> \<Rightarrow> bool" (* an arbitary Boolean algebra*)
consts ar_element:: "'w \<sigma>"         (* an arbitary elemnt in the Boolean algebra*)
axiomatization where
A1: "boolean_algebra ar_Bool_al" and
A2: "\<forall>a b. a \<prec> b \<longrightarrow> ar_Bool_al a \<and> ar_Bool_al b" and
A3: "ar_Bool_al ar_element"

(*Finding quasi contermodel, can not prove yet *)
lemma AND_DD: "AND sub \<longrightarrow> DD sub" nitpick  oops
lemma OR_UD: "OR sub \<longrightarrow> UD sub" nitpick oops

(*The image of a subordination relation is filter and the inverse image an ideal (?)*)
lemma im_filter: "filter_boolean (\<lambda>x.  ar_element  \<prec> x )" nitpick oops
lemma im_ideal : "ideal_boolean (\<lambda>x. x \<prec> ar_element )"   nitpick oops
(*David: however, adding a reflexivity restriction we get no counterexample.
  In case this is a theorem: is reflexivity really required?*)
lemma "reflexive \<rho> \<and> (WO \<rho> \<and> DD \<rho>) \<longrightarrow>  (\<forall>x y. (\<rho> \<^bold>\<diamond> y  \<^bold>\<preceq> x) \<longrightarrow> \<rho> y x)"
  (*nitpick[timeout=100]*) 
  apply auto
  unfolding slanted_diamond_def 
  unfolding reflexive_def
  unfolding WO_def DD_def
  (* unfolding subset_def  *)
  (* sledgehammer[verbose] *) oops (*sledgehammer magic not working yet ...*)
lemma "(WO \<rho> \<and> DD \<rho> )  \<longrightarrow>  (\<forall>a b. (\<exists>x z y. \<rho> a x \<and> \<rho> b z \<and> (\<rho> (a\<^bold>\<or>b) y)) 
\<longrightarrow>  ((\<rho> \<^bold>\<diamond> (a \<^bold>\<or> b)) \<^bold>\<preceq> ((\<rho> \<^bold>\<diamond> a) \<^bold>\<or> (\<rho> \<^bold>\<diamond> b)) \<longrightarrow> OR \<rho>))" 
  unfolding WO_def and DD_def and  OR_def and slanted_diamond_def  oops (*Why counter model ?*)

*)