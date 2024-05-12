theory contact_algebra
  imports subordination_algebra  slanted_obligation

begin

declare[[show_types=false]] (*switch this on/off to see the actual types (useful to debug polymorphism problems)*)

(*Input/output rules*)
definition AND_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>AND_con \<rho> \<equiv> \<forall>a x y. \<rho> a (x\<^bold>\<or>y)\<longrightarrow> (\<rho> a y \<or> \<rho> a x) \<close> 
definition OR_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>OR_con \<rho> \<equiv> \<forall>a b x. \<rho>  (a\<^bold>\<or>b) x\<longrightarrow> (\<rho> a x \<or> \<rho> b x) \<close>
definition SI_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>SI_con \<rho> \<equiv> \<forall>a b x. \<rho> a x \<and> (a \<^bold>\<preceq> b)\<longrightarrow> \<rho> b x\<close> 
definition WO_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>WO_con \<rho> \<equiv> \<forall>a x y. \<rho> a x \<and> (x \<^bold>\<preceq> y)\<longrightarrow> \<rho> a y\<close>
definition Top_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Top_con \<rho> \<equiv> \<not> \<rho> \<^bold>\<top> \<^bold>\<bottom> \<close>
definition Bot_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Bot_con \<rho> \<equiv>\<not> \<rho> \<^bold>\<bottom> \<^bold>\<top>\<close>
definition SF_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>SF_con \<rho> \<equiv> \<forall>x. \<exists>y.\<not> \<rho> x y  \<close> 
definition SB_con::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>SB_con \<rho> \<equiv> \<forall>x. \<exists>y.\<not> \<rho> y x  \<close>

(*Subordination to precontact algebras*)
lemma subtoconsf:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SF_con \<sigma> "  unfolding subordination_def 
  by (smt (verit, del_insts) SF_con_def SF_def)
lemma subtoconsb:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SB_con \<sigma> "  unfolding subordination_def and SB_con_def and SB_def 
  by (metis BA_dn) 
lemma subtocontop:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> Top_con \<sigma> " unfolding subordination_def 
  by (metis BA_dn Top_con_def Top_def fp_dc fp_dc_rel fp_rel ofp_dc op_dual_def op_equal_equ setequ_equ)
lemma subtoconbot:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> Bot_con \<sigma> " unfolding subordination_def 
  by (metis BA_dn Bot_con_def Bot_def fp_dc fp_dc_rel fp_rel ofp_dc op_dual_def op_equal_equ setequ_equ)
lemma subtoconwo:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> WO_con \<sigma> " unfolding subordination_def 
  by (smt (verit) BA_deMorgan2 BA_dn L10 L3 WO_con_def WO_def setequ_equ)
lemma subtoconsi:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SI_con \<sigma> " unfolding SI_con_def and SI_def 
  by (metis BA_dn SI_def subordination_def)
lemma subtoconand:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> AND_con \<sigma> " unfolding AND_con_def and AND_def 
  by (metis AND_def BA_deMorgan1 BA_dn subordination_def)
lemma subtoconor:"(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> OR_con \<sigma> " unfolding OR_con_def and OR_def  
  by (metis BA_dn OR_def subordination_def)

definition precontact : "precontact \<rho> \<equiv> AND_con \<rho> \<and> OR_con \<rho> \<and> SI_con \<rho> \<and> WO_con \<rho> \<and> Bot_con \<rho> \<and> Top_con \<rho> \<and> SF_con \<rho> \<and> SB_con \<rho>"

lemma subtoconth: "(subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> (precontact \<sigma>)"  
  by (simp add: precontact subtoconand subtoconbot subtoconor subtoconsb subtoconsf subtoconsi subtocontop subtoconwo)

(*Precontact to subordination algebras*)
lemma contosubsf :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SF \<sigma> "  
  unfolding precontact  by (metis BA_dn SF_con_def SF_def)
lemma contosubsb :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SB \<sigma> "  
  by (simp add: SB_con_def SB_def precontact)
lemma contosubtop :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> Top \<sigma> "  
  by (smt (z3) Top_con_def Top_def dom_compl_invol fp_dc fp_dc_rel fp_rel iDM_a iDM_b ofp_dc op_dual_def op_equal_equ precontact recall_that setequ_equ)  
lemma contosubbot :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> Bot \<sigma> "  
  by (smt (z3) Bot_con_def Bot_def dom_compl_invol fp_c fp_c_rel fp_dc fp_rel iDM_a iDM_b ofp_dc op_equal_equ precontact recall_that setequ_equ)
lemma contosubsi :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SI \<sigma> " 
  by (smt (z3) SI_con_def SI_def precontact)
lemma contosubwi :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> WO \<sigma> "  
  by (smt (z3) BA_deMorgan2 L10 L3 WO_con_def WO_def precontact setequ_equ)
lemma contosubor :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> OR \<sigma> "  
  by (metis OR_con_def OR_def precontact)
lemma contosuband :"(precontact \<rho>  \<and>  (\<forall> a x. \<sigma> a x \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> AND \<sigma> "  
  by (smt (z3) AND_con_def AND_def BA_deMorgan2 precontact)


definition subtocon::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open> subtocon \<rho> \<sigma> \<equiv> (\<forall> a x. (\<rho> a x) \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) ) \<close>
definition contosub::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open> contosub \<rho> \<sigma> \<equiv> (\<forall> a x. (\<sigma> a x) \<longleftrightarrow> \<not>(\<rho> a(\<^bold>\<midarrow>x)) ) \<close>
(*
lemma subconeq:" \<forall> x y.  (contosub  (subtocon \<rho>))  x y \<longrightarrow> \<rho> x y  "
*)


definition CS1 ::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where \<open>CS1 \<rho> \<sigma> \<equiv>((subordination \<rho>) \<and> (precontact \<sigma>)) \<longrightarrow> (\<forall>a x y. ((\<rho> a (x \<^bold>\<or> y))  \<and> (\<not> (\<sigma> a x)) ) \<longrightarrow> (\<rho> a y ))\<close> 
definition CS2 ::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where \<open>CS2 \<rho> \<sigma> \<equiv>((subordination \<rho>) \<and> (precontact \<sigma>)) \<longrightarrow> (\<forall>a x y. (\<not> (\<sigma> a (x \<^bold>\<and> y))  \<and> (\<rho> a x) ) \<longrightarrow> \<not>(\<sigma> a y ))\<close> 

lemma sublecon: "( subordination \<rho> \<and> precontact \<sigma> \<and>  CS1 \<rho> \<sigma> \<and>  CS2 \<rho> \<sigma>) \<longrightarrow> (\<forall> a x.  \<not>(\<sigma> a(\<^bold>\<midarrow>x)) \<longrightarrow> ( \<rho> a x)) " 
unfolding CS1_def subordination_def   using  SI_def Top_def WO_def compl_def setequ_equ subset_def top_def meet_def BA_deMorgan2 oops
  
end 