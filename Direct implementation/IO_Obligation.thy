theory IO_Obligation imports IO_LogicalBase
begin
definition  monotone :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where  "monotone op \<equiv> (\<forall> \<phi> \<psi>. ( (\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> ((op \<phi>) \<^bold>\<le> (op \<psi>)) ) )"
definition  regular_dia :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "regular_dia op \<equiv>   (\<forall> \<phi> \<psi>. ((op (\<phi> \<^bold>\<or> \<psi>)) = ((op \<phi>) \<^bold>\<or> (op \<psi>))))"
definition  regular_box :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "regular_box op \<equiv>   (\<forall> \<phi> \<psi>. op (\<phi> \<^bold>\<and> \<psi>) = (op \<phi> \<^bold>\<and> op \<psi>))"
definition normal_dia ::  "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "normal_dia op \<equiv> regular_dia op \<and> op \<^bold>\<bottom> = \<^bold>\<bottom>"
definition normal_box :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "normal_box op  \<equiv> regular_box op \<and>  op \<^bold>\<top>  = \<^bold>\<top>"
definition tense_ob :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "tense_ob op1 op2 \<equiv> \<forall> \<phi> \<psi>. op1 \<phi> \<^bold>\<le> \<psi> \<longleftrightarrow> \<phi> \<^bold>\<le> op2 \<psi>"

lemma regulartomonotone: " regular_dia op \<longrightarrow>monotone op" using ORDERtoOR  
  by (metis monotone_def ORtoORDER regular_dia_def) 
lemma largestTOregular2: "monotone op  \<longrightarrow> regular_dia op" nitpick oops
 
lemma tenstonormal: "tense_ob \<^bold>\<diamond>\<^sub>o \<^bold>\<box>\<^sub>o \<longrightarrow> regular_dia \<^bold>\<diamond>\<^sub>o" oops


consts IO1 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>1\<^sub>o")
consts IO2 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>2\<^sub>o")
consts IO3 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>3\<^sub>o")
consts IO4 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>4\<^sub>o")

axiomatization where 
ax_IO1 : "monotone \<^bold>\<diamond>\<^sup>1\<^sub>o" and
ax_IO2 : "regular_dia \<^bold>\<diamond>\<^sup>2\<^sub>o" and
ax_IO3i : "monotone \<^bold>\<diamond>\<^sup>3\<^sub>o" and
ax_IO3ii : "(\<^bold>\<diamond>\<^sup>3\<^sub>o \<phi>) \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>o (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>o \<phi>)" and
ax_IO4i : "regular_dia \<^bold>\<diamond>\<^sup>4\<^sub>o" and
ax_IO4ii : "(\<^bold>\<diamond>\<^sup>4\<^sub>o \<phi>) \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>o (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>4\<^sub>o \<phi>)" 

(*
axIO1Nonempty: "\<exists>\<phi>. \<^bold>\<diamond>\<^sup>1\<^sub>o \<phi> \<noteq> \<^bold>\<bottom>" and
axIO2Nonempty: "\<exists>\<phi>. \<^bold>\<diamond>\<^sup>2\<^sub>o \<phi> \<noteq> \<^bold>\<bottom>"
*)


(*Soundness out1*)
lemma IO1top: "\<^bold>\<diamond>\<^sup>1\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top> " by (meson settrue_def) 
lemma IO1SI: "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<beta> \<^bold>\<le> \<alpha>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o\<beta> \<^bold>\<le> \<phi>) " using monotone_def ax_IO1  by force
lemma IO1WO: "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi> ) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<psi>) " by simp
lemma IO1AND: "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<psi> ) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le>  (\<phi>\<^bold>\<and>\<psi>)) " by (simp add: setand_def)
 
(*Soundness out2*)
lemma IO2top: "\<^bold>\<diamond>\<^sup>2\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top> "  by (simp add: settrue_def)
lemma IO2SI: "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<beta> \<^bold>\<le> \<alpha>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o\<beta> \<^bold>\<le> \<phi>) "  using regulartomonotone  
  using monotone_def ax_IO2 by fastforce
lemma IO2WO: "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<phi> \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<psi>) "  by simp
lemma IO2AND: "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<psi> ) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le>  (\<phi>\<^bold>\<and>\<psi>)) " by (simp add: setand_def)
lemma IO2OR: "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<beta> \<^bold>\<le> \<phi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o(\<alpha>\<^bold>\<or>\<beta>) \<^bold>\<le>  \<phi>) " 
  using ax_IO2 regular_dia_def regular_dia_def setor_def by auto

(*Soundness out3*)
lemma IO3top: "\<^bold>\<diamond>\<^sup>3\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top> " by (simp add: settrue_def)
lemma IO3SI: "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi> ) \<and> (\<beta> \<^bold>\<le> \<alpha>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o\<beta> \<^bold>\<le> \<phi>) "  
  using monotone_def ax_IO3i by fastforce
lemma IO3WO: "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>) " by simp
lemma IO3AND: "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le>  (\<phi>\<^bold>\<and>\<psi>)) "  by (simp add: setand_def)
lemma IO3CT: "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o (\<alpha> \<^bold>\<and> \<phi>) \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<psi>)" 
  using   monotone_def ax_IO3i ax_IO3ii  setand_def by (smt (verit, ccfv_threshold))
 
(*Soundness out4*)
lemma IO4top: "\<^bold>\<diamond>\<^sup>4\<^sub>o \<^bold>\<top> \<^bold>\<le> \<^bold>\<top> " by (simp add: settrue_def)
lemma IO4SI: "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<beta> \<^bold>\<le> \<alpha>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o\<beta> \<^bold>\<le> \<phi>) " using regulartomonotone   
  using monotone_def ax_IO4i by fastforce
lemma IO4WO: "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<phi> \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>) " by auto
lemma IO4AND: "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o\<alpha> \<^bold>\<le> (\<phi>\<^bold>\<and>\<psi>)) " using setand_def by auto
lemma IO4OR : "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<beta> \<^bold>\<le> \<phi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o(\<alpha>\<^bold>\<or>\<beta>) \<^bold>\<le>  \<phi>) "  
  using ax_IO4i regular_dia_def regular_dia_def setor_def by auto
lemma IO4CT: "((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>4\<^sub>o (\<alpha> \<^bold>\<and> \<phi>) \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<psi>)"     
  using  monotone_def ax_IO4i ax_IO4ii setand_def regulartomonotone by (smt (verit, ccfv_threshold)) (* sledgehammer[verbose, timeout=180 ]*)
   
(*Counter Models*)
lemma IO1OR: "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<beta> \<^bold>\<le> \<phi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o(\<alpha>\<^bold>\<or>\<beta>) \<^bold>\<le> \<phi>)" nitpick  oops
lemma IO3OR: "((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>3\<^sub>o \<beta> \<^bold>\<le> \<phi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>3\<^sub>o(\<alpha>\<^bold>\<or>\<beta>) \<^bold>\<le> \<phi>) " nitpick  oops
lemma IO1CT: "((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>1\<^sub>o (\<alpha> \<^bold>\<and> \<phi>) \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<psi>)" nitpick oops
lemma IO2CT: "((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<^bold>\<diamond>\<^sup>2\<^sub>o (\<alpha> \<^bold>\<and> \<phi>) \<^bold>\<le> \<psi>) ) \<longrightarrow> (\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<psi>)" nitpick oops


end