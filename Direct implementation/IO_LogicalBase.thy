theory IO_LogicalBase imports Main
begin

(*----------- Technicalities--------*)
declare[[smt_timeout=30]]
declare[[show_types]]
(* declare[[syntax_ambiguity_warning=false]] *)
sledgehammer_params[isar_proof=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3, atoms=a b c d] (*default Nitpick settings*)

typedecl i (* type for possible worlds *)  
type_synonym \<tau> = "(i\<Rightarrow>bool)"
consts r :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r"70) (* relation for a modal logic K *)

consts diaOb :: "\<tau>\<Rightarrow>\<tau>"  ("\<^bold>\<diamond>\<^sub>o")
consts boxOb :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<box>\<^sub>o")
consts diaPr :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<diamond>\<^sub>p")
consts boxPr ::  "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<box>\<^sub>p")
consts diadPr :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<diamond>\<^sub>d\<^sub>p")
consts boxdPr ::  "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<box>\<^sub>d\<^sub>p")

definition setnot   :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_"[52]53)         where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
definition setor    :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<or>"50)    where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)" 
definition setand   :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<and>"51)    where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)" 
definition setimp   :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<longrightarrow>"49)  where "\<phi>\<^bold>\<longrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w)"
definition setcoimp   :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr "\<^bold>\<hookleftarrow>"52)  where "\<phi>\<^bold>\<hookleftarrow>\<psi> \<equiv> \<lambda>w. (\<phi>(w) \<and> \<not>\<psi>(w)) "
definition setbox   :: "\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<box>\<^sub>k")               where "\<^bold>\<box>\<^sub>k\<phi> \<equiv> \<lambda>w. \<forall>v. w r v \<longrightarrow> \<phi>(v)"
definition settrue  :: "\<tau>" ("\<^bold>\<top>")                  where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
definition setfalse :: "\<tau>" ("\<^bold>\<bottom>")                  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 
definition setvalid :: "\<tau>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)     where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p(w)" (* global validity *)


abbreviation(input) msubset :: "\<tau>\<Rightarrow>\<tau>\<Rightarrow>bool" (infix "\<^bold>\<le>" 53) where "\<phi> \<^bold>\<le> \<psi> \<equiv> \<forall>x. \<phi> x \<longrightarrow> \<psi> x"
abbreviation(input) msubsetrelation :: "(\<tau>\<Rightarrow>\<tau>)\<Rightarrow>(\<tau>\<Rightarrow>\<tau>)\<Rightarrow> bool" (infix "\<^bold>\<subseteq>" 54) where "op1 \<^bold>\<subseteq> op2 \<equiv> \<forall>\<phi>.(\<forall> \<psi>.  op1 \<phi> = \<psi> \<longrightarrow>  op2 \<phi> = \<psi>) "
 

lemma ANDtoORDER: "(\<phi>\<^bold>\<and>\<psi>) = \<phi> \<longrightarrow> (\<phi> \<^bold>\<le> \<psi>)"  by (metis setand_def)
lemma ORtoORDER: "(\<phi>\<^bold>\<or>\<psi>) = \<psi> \<longrightarrow> (\<phi> \<^bold>\<le> \<psi>)" by (metis setor_def)
lemma ORDERtoAND: "(\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> (\<phi>\<^bold>\<and>\<psi>) = \<phi>  " using setand_def by auto
lemma ORDERtoOR: "(\<phi> \<^bold>\<le> \<psi>) \<longrightarrow> (\<phi>\<^bold>\<or>\<psi>) = \<psi> " using setor_def by auto


lemma coimplication1: "((\<phi>\<^bold>\<hookleftarrow>\<psi>) \<^bold>\<le> \<chi>) \<longrightarrow> (\<phi> \<^bold>\<le> (\<psi> \<^bold>\<or> \<chi>) )"  
  using setcoimp_def setor_def by auto
lemma coimplication2: "(\<phi> \<^bold>\<le> (\<psi> \<^bold>\<or> \<chi>) )\<longrightarrow> ((\<phi>\<^bold>\<hookleftarrow>\<psi>) \<^bold>\<le> \<chi>)  "  
  by (metis setcoimp_def setor_def)
end