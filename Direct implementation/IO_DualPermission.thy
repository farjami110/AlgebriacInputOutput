theory IO_DualPermission 
  imports IO_LogicalBase IO_Obligation IO_Permission
begin

definition regular_dpr :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "regular_dpr op \<equiv> \<forall> \<phi> \<psi>. ((op (\<phi> \<^bold>\<and> \<psi>)) = ((op \<phi>) \<^bold>\<or> (op \<psi>)))"
definition normal_dpr ::  "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "normal_dpr op \<equiv> regular_dpr op \<and> op \<^bold>\<top> = \<^bold>\<bottom>"
definition tense_dpr :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>bool" where "tense_dpr op1 op2 \<equiv> \<forall> \<phi> \<psi>. op1 \<phi> \<^bold>\<le> \<psi> \<longleftrightarrow> op2 \<psi> \<^bold>\<le> \<phi>"

lemma regulartoantitone: " regular_dpr op \<longrightarrow> antitone op "unfolding regular_dpr_def antitone_def using ORDERtoAND 
  by (metis setor_def)

consts IODP1 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p")
consts IODP2 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p")
consts IODP3 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p")
consts IODP4 :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p")

axiomatization where 
ax_IODP1 : "antitone \<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p" and
ax_IODP2 : "regular_dpr \<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p" and
ax_IODP3i : "antitone \<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p" and
ax_IODP3ii : "(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<phi>) \<^bold>\<le> \<^bold>\<diamond>\<^sup>3\<^sub>o( (\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<phi>)\<^bold>\<hookleftarrow>\<phi> )" and
ax_IODP4i : "regular_dpr \<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p" and
ax_IODP4ii : "(\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<phi>) \<^bold>\<le> \<^bold>\<diamond>\<^sup>4\<^sub>o( (\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<phi>)\<^bold>\<hookleftarrow>\<phi> )"

(*Soundness out1*)
lemma IODP1TOP: "\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p \<^bold>\<bottom> \<^bold>\<le> \<^bold>\<top>"  by (simp add: settrue_def) 
lemma IODP1SI: "((\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p \<alpha> \<^bold>\<le> \<phi>)\<and>(\<alpha>\<^bold>\<le>\<beta>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<beta> \<^bold>\<le>\<phi>)"  by (metis antitone_def ax_IODP1)
lemma IODP1WO: "((\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha> \<^bold>\<le>\<phi>)\<and>(\<phi>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)"  by simp
lemma IODP1AND: "((\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>(\<phi>\<^bold>\<and>\<psi>))" by (simp add: setand_def)


(*Soundness out2*)
lemma IODP2TOP: "\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p \<^bold>\<bottom> \<^bold>\<le> \<^bold>\<top>"  by (simp add: settrue_def)
lemma IODP2SI: "((\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p \<alpha> \<^bold>\<le> \<phi>)\<and>(\<alpha>\<^bold>\<le>\<beta>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<beta> \<^bold>\<le>\<phi>)" by (metis ORDERtoAND ax_IODP2 regular_dpr_def setor_def)
lemma IODP2WO: "((\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha> \<^bold>\<le>\<phi>)\<and>(\<phi>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)"  by simp
lemma IODP2AND: "((\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>(\<phi>\<^bold>\<and>\<psi>))" by (simp add: setand_def)
lemma IODP2OR: "((\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<beta>\<^bold>\<le>\<phi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p(\<alpha>\<^bold>\<and>\<beta>)\<^bold>\<le>\<phi>)"  using ax_IODP2 regular_dpr_def setor_def by auto

(*Soundness out3*)
lemma IODP3TOP: "\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p \<^bold>\<bottom> \<^bold>\<le> \<^bold>\<top>" by (simp add: settrue_def)
lemma IODP3SI: "((\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p \<alpha> \<^bold>\<le> \<phi>)\<and>(\<alpha>\<^bold>\<le>\<beta>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<beta> \<^bold>\<le>\<phi>)" using antitone_def ax_IODP3i by force
lemma IODP3WO: "((\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha> \<^bold>\<le>\<phi>)\<and>(\<phi>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)" by simp
lemma IODP3AND: "((\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>(\<phi>\<^bold>\<and>\<psi>))" by (simp add: setand_def)
lemma IODP3CT: "((\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>3\<^sub>o(\<phi>\<^bold>\<hookleftarrow>\<alpha>)\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)"  
  by (smt (verit) monotone_def ax_IO3i ax_IODP3ii setcoimp_def)  


(*Soundness out4*)
lemma IODP4TOP: "\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p \<^bold>\<bottom> \<^bold>\<le> \<^bold>\<top>" by (simp add: settrue_def)
lemma IODP4SI:  "( ((\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p \<alpha>) \<^bold>\<le> \<phi>) \<and> (\<alpha>\<^bold>\<le>\<beta>) )\<longrightarrow>((\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<beta>) \<^bold>\<le>\<phi>)"  
  using regulartoantitone using antitone_def ax_IODP4i by fastforce
lemma IODP4WO: "((\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha> \<^bold>\<le>\<phi>)\<and>(\<phi>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)"  by simp
lemma IODP4AND: "((\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>(\<phi>\<^bold>\<and>\<psi>))"by (simp add: setand_def)
lemma IODP4CT: "((\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>4\<^sub>o(\<phi>\<^bold>\<hookleftarrow>\<alpha>)\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>4\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)" 
  using  monotone_def ax_IO4i ax_IODP4ii regulartomonotone setcoimp_def  by (smt (verit, ccfv_threshold))
 
(*Counter Models*)
lemma IODP1OR: "((\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<beta>\<^bold>\<le>\<phi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p(\<alpha>\<^bold>\<and>\<beta>)\<^bold>\<le>\<phi>)" nitpick oops
lemma IODP3OR: "((\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p\<beta>\<^bold>\<le>\<phi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>3\<^sub>d\<^sub>p(\<alpha>\<^bold>\<and>\<beta>)\<^bold>\<le>\<phi>)" nitpick oops
lemma IODP1CT: "((\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>1\<^sub>o(\<phi>\<^bold>\<hookleftarrow>\<alpha>)\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>1\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)" nitpick oops
lemma IODP2CT: "((\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<phi>)\<and>(\<^bold>\<diamond>\<^sup>2\<^sub>o(\<phi>\<^bold>\<hookleftarrow>\<alpha>)\<^bold>\<le>\<psi>))\<longrightarrow>(\<^bold>\<diamond>\<^sup>2\<^sub>d\<^sub>p\<alpha>\<^bold>\<le>\<psi>)" nitpick oops

end