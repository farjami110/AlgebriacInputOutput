theory IO_Permission 
  imports IO_LogicalBase IO_Obligation

begin


definition antitone :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where  "antitone op \<equiv> \<forall> \<phi> \<psi>. ( (\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> (op \<psi>) \<^bold>\<le> (op \<phi>))"
definition regular_pr :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "regular_pr op \<equiv> \<forall> \<phi> \<psi>. op (\<phi> \<^bold>\<or> \<psi>) = (op \<phi> \<^bold>\<and> op \<psi>)"
definition normal_pr ::  "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "normal_pr op \<equiv> regular_pr op \<and> op \<^bold>\<bottom> = \<^bold>\<top>"
definition tense_pr :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "tense_pr op1 op2 \<equiv> \<forall> \<phi> \<psi>.  \<phi> \<^bold>\<le> op1 \<psi> \<longleftrightarrow> \<psi> \<^bold>\<le> op2 \<phi>"

consts IOP1 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>1\<^sub>p")
consts IOP2 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>2\<^sub>p")
consts IOP3 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>3\<^sub>p")
consts IOP4 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>4\<^sub>p")

axiomatization where 
ax_IOP1 : "antitone \<^bold>\<diamond>\<^sup>1\<^sub>p" and
ax_IOP2 : "regular_pr \<^bold>\<diamond>\<^sup>2\<^sub>p" and
ax_IOP3i : "antitone \<^bold>\<diamond>\<^sup>3\<^sub>p" and
ax_IOP3ii : "\<^bold>\<diamond>\<^sup>3\<^sub>p (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>3\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond>\<^sup>3\<^sub>p \<phi>)" and
ax_IOP4i : "regular_pr \<^bold>\<diamond>\<^sup>4\<^sub>p" and
ax_IOP4ii : "\<^bold>\<diamond>\<^sup>4\<^sub>p (\<phi> \<^bold>\<and> \<^bold>\<diamond>\<^sup>4\<^sub>o \<phi>) \<^bold>\<le> (\<^bold>\<diamond>\<^sup>4\<^sub>p \<phi>)"

(*Soundness out1*)
lemma IO1PTOP: "\<^bold>\<bottom> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<^bold>\<top> " by (simp add: setfalse_def)
lemma IO1PSI: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<beta>) \<and> (\<alpha> \<^bold>\<le> \<beta>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p \<alpha>)"   
  using antitone_def ax_IOP1 by fastforce
lemma IO1PWO: "((\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>)" by simp
lemma IO1PAND: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>)) \<longrightarrow> ((\<phi>\<^bold>\<or>\<psi>)\<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>)" by (simp add: setor_def)

(*Soundness out2*)
lemma IO2PTOP: "\<^bold>\<bottom> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<^bold>\<top> " by (simp add: setfalse_def)
lemma IO2PSI: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<beta>) \<and> (\<alpha> \<^bold>\<le> \<beta>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p \<alpha>)" 
  unfolding regular_pr_def 
  by (metis ORDERtoOR ax_IOP2 regular_pr_def setand_def)
lemma IO2PWO: "((\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>)"  by simp
lemma IO2PAND: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>)) \<longrightarrow> ((\<phi>\<^bold>\<or>\<psi>)\<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>)"  by (simp add: setor_def)
lemma IO2POR: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<beta>))  \<longrightarrow> (\<phi> \<^bold>\<le>  \<^bold>\<diamond>\<^sup>2\<^sub>p(\<alpha>\<^bold>\<or>\<beta>) )"  using ax_IOP2  
  by (simp add: regular_pr_def setand_def)
   
(*Soundness out3*)
lemma IO3PTOP: "\<^bold>\<bottom> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<^bold>\<top> " by (simp add: setfalse_def)
lemma IO3PSI: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<beta>) \<and> (\<alpha> \<^bold>\<le> \<beta>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p \<alpha>)" using  ax_IOP3i 
  using antitone_def by fastforce
lemma IO3PWO: "((\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>)" by simp
lemma IO3PAND: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>)) \<longrightarrow> ((\<phi>\<^bold>\<or>\<psi>)\<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>)" by (simp add: setor_def)
lemma IO3PCT: " ((\<^bold>\<diamond>\<^sup>3\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p (\<alpha>\<^bold>\<and>\<phi>))) \<longrightarrow> (\<psi> \<^bold>\<le>  \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>)"  using ax_IOP3i oops

(*Soundness out4*)
lemma IO4PTOP: "\<^bold>\<bottom> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<^bold>\<top> " by (simp add: setfalse_def)
lemma IO4PSI: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<beta>) \<and> (\<alpha> \<^bold>\<le> \<beta>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p \<alpha>)"   using ax_IOP1  
  by (metis ORDERtoOR ax_IOP4i regular_pr_def setand_def)
lemma IO4WO: "((\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<psi>)) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<alpha>)" by simp
lemma IO4PAND: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<alpha>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<alpha>)) \<longrightarrow> ((\<phi>\<^bold>\<or>\<psi>)\<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<alpha>)" by (simp add: setor_def)
lemma IO4PCT: " ((\<^bold>\<diamond>\<^sup>4\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p (\<alpha>\<^bold>\<and>\<phi>))) \<longrightarrow> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>p\<alpha>)"  using ax_IOP4i oops

(*Counter Models*)
lemma IO1POR: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<beta>))  \<longrightarrow> (\<phi> \<^bold>\<le>  \<^bold>\<diamond>\<^sup>1\<^sub>p(\<alpha>\<^bold>\<or>\<beta>) )" nitpick oops
lemma IO3POR: "((\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<alpha>) \<and> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>p\<beta>))  \<longrightarrow> (\<phi> \<^bold>\<le>  \<^bold>\<diamond>\<^sup>3\<^sub>p(\<alpha>\<^bold>\<or>\<beta>) )" nitpick oops
lemma IO1PCT: " ((\<^bold>\<diamond>\<^sup>1\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p (\<alpha>\<^bold>\<and>\<phi>))) \<longrightarrow> (\<psi> \<^bold>\<le>  \<^bold>\<diamond>\<^sup>1\<^sub>p\<alpha>)" nitpick oops
lemma IO2PCT: " ((\<^bold>\<diamond>\<^sup>2\<^sub>o \<alpha> \<^bold>\<le> \<phi>) \<and> (\<psi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p (\<alpha>\<^bold>\<and>\<phi>))) \<longrightarrow> (\<psi> \<^bold>\<le>  \<^bold>\<diamond>\<^sup>2\<^sub>p\<alpha>)" nitpick oops
lemma IOP1toIOP2: "(\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>1\<^sub>p\<beta>) \<longrightarrow> (\<phi> \<^bold>\<le> \<^bold>\<diamond>\<^sup>2\<^sub>p\<beta>)" nitpick[user_axioms=true] oops
end