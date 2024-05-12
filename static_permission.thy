theory static_permission
  imports slanted_permission

begin

(*Static Permission*)

definition AND_st::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where \<open>AND_st \<rho> \<sigma> \<equiv>(subordination \<rho>)\<and> (\<forall>a  x y. ((\<rho> a x)  \<and> (\<sigma> a y) ) \<longrightarrow> (\<sigma> a (x\<^bold>\<and>y)))\<close> 

definition OR_st::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where \<open>OR_st \<rho> \<sigma> \<equiv> (subordination \<rho>) \<and> (\<forall>a b x. \<rho> a x \<and> (\<sigma> b x) \<longrightarrow> (\<sigma> (a\<^bold>\<or>b) x))\<close> 

definition Ctop::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Ctop \<rho> \<equiv> (\<rho> \<^bold>\<top> \<^bold>\<top>)\<close>
definition Cbot::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Cbot \<rho> \<equiv> (\<rho> \<^bold>\<bottom> \<^bold>\<bottom>)\<close>   

definition permission_st::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where "permission_st \<rho> \<sigma> \<equiv> subordination \<rho> \<and> (\<forall> a x. \<rho> a x \<longrightarrow> \<sigma> a x)\<and> Ctop \<sigma> \<and> Cbot \<sigma> \<and> SI \<sigma> \<and> WO \<sigma> \<and> AND_st \<rho> \<sigma> \<and> OR_st \<rho> \<sigma> "



(*The expriment here shows a modal translation for static permission, it is different from the one in the paper*)

(*Modal translation for (AND)\<^sup>\<down> in static permission*)
lemma thsubancon4: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall> a b c.  (\<rho> a b \<and> \<sigma> a c  ) \<longrightarrow> \<sigma> a (b\<^bold>\<and>c) ) \<longrightarrow> (\<forall>a. \<exists>b. ( (\<rho> \<^bold>\<diamond> a ) \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> b  ) )  ) " 
  unfolding subordination_def and precontact  Bot_con_def L13 L3 L5 precon_diamond_def setequ_def setequ_equ sup_char
  by (metis SB_con_def sup_char)

lemma thsubancon5: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall>a. \<exists>b.\<not> ((\<rho> \<^bold>\<diamond> a ) \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> b  ) ) \<longrightarrow> (\<forall> a b c.  (\<rho> a b \<and> \<sigma> a c  ) \<longrightarrow> \<sigma> a (b\<^bold>\<and>c) ) ) " 
  unfolding subordination_def and precontact  Bot_con_def L13 L3 L5 precon_diamond_def setequ_def setequ_equ sup_char
  by (metis Bot_def bottom_def inf_char slanted_diamond_def subset_def)

(*Modal translation for (OR)\<^sup>\<down> in static permission*)
lemma thsubancon6: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall> a b x.  (\<rho> a x \<and> \<sigma> b x  ) \<longrightarrow> \<sigma> (a\<^bold>\<or>b) x ) \<longrightarrow> (\<exists>b. \<forall>a.( \<^bold>\<midarrow> (\<sigma> \<^bold>\<rhd> b)  \<^bold>\<preceq> \<^bold>\<midarrow> (\<rho> \<^bold>\<diamond> a ) ) )  ) " 
unfolding subordination_def and precontact 
  by (metis (mono_tags, lifting) BA_cp Bot_con_def precon_diamond_def subset_def supremum_def top_def)

lemma thsubancon7: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<exists>b. \<forall>a.( \<^bold>\<midarrow> (\<sigma> \<^bold>\<rhd> b)  \<^bold>\<preceq> \<^bold>\<midarrow> (\<rho> \<^bold>\<diamond> a ) ) )  \<longrightarrow>  (\<forall> a b x.  (\<rho> a x \<and> \<sigma> b x  ) \<longrightarrow> \<sigma> (a\<^bold>\<or>b) x ) ) " 
unfolding subordination_def and precontact 
  by (metis (no_types, lifting) SI_con_def join_def subset_def)

(*Modal translation for (CT)\<^sup>\<up> in static permission*)
lemma thsubancon8: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall> a x y.  (\<rho> a x \<and> \<sigma> (a\<^bold>\<and>x) y ) \<longrightarrow> \<sigma> a (x\<^bold>\<and>y) ) \<longrightarrow> (   \<exists>b.  \<forall>a. (\<sigma> \<^bold>\<rhd> a)  \<^bold>\<preceq> (\<rho> \<^bold>\<box> (\<sigma> \<^bold>\<rhd> b) ) )  ) " 
  unfolding subordination_def and precontact SB_con_def SF_def WO_def le31it1b precon_diamond_def subset_def sup_char top_def 
  slanted_box_def subset_def sup_char  
  by (metis (mono_tags, lifting) Bot_con_def subset_def sup_char top_def)

lemma thsubancon9: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
(  (       \<forall>b. \<exists>a. \<not> ( (\<sigma> \<^bold>\<rhd> a)  \<^bold>\<preceq>  (\<rho> \<^bold>\<box> (\<sigma> \<^bold>\<rhd> b)) ) )  )\<longrightarrow>  (\<forall> a x y.  (\<rho> a x \<and> \<sigma> (a\<^bold>\<and>x) y ) \<longrightarrow> \<sigma> a (x\<^bold>\<and>y) ) " 
  unfolding subordination_def and precontact SB_con_def SF_def WO_def le31it1b precon_diamond_def subset_def sup_char top_def 
  slanted_box_def subset_def sup_char 
  by (metis L10 L13 setequ_equ sup_char top_def)



end