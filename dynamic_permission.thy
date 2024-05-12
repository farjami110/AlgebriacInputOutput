theory dynamic_permission
  imports slanted_permission static_permission

begin
(*Dynamic Permission*)
definition SI_in::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>SI_in \<rho> \<equiv> \<forall>a b x. \<rho> a x \<and> (a \<^bold>\<preceq> b)\<longrightarrow> \<rho> b x\<close> 
definition WO_in::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>WO_in \<rho> \<equiv> \<forall>a x y. \<rho> a x \<and> (x \<^bold>\<preceq> y)\<longrightarrow> \<rho> a y\<close> 
definition AND_in::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>AND_in \<rho> \<sigma> \<equiv>(subordination \<rho>)\<and> (\<forall>a  x y. ((\<rho> a x)  \<and> (\<sigma> a (\<^bold>\<midarrow>(x\<^bold>\<and>y))) ) \<longrightarrow> (\<sigma> a (\<^bold>\<midarrow> y)))\<close> 
definition OR_in::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>OR_in \<rho> \<sigma> \<equiv> (subordination \<rho>) \<and> (\<forall>a b x. \<rho> a x \<and> (\<sigma> (a\<^bold>\<or>b)(\<^bold>\<midarrow>x)) \<longrightarrow> (\<sigma> b(\<^bold>\<midarrow>x)))\<close> 
definition Top_in::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Top_in \<rho> \<equiv> \<forall> a x. (\<rho> \<^bold>\<bottom> \<^bold>\<top> )\<longrightarrow> (\<rho> a x) \<close>
definition Bot_in::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Bot_in \<rho> \<equiv> \<forall> a x. (\<rho> \<^bold>\<top> \<^bold>\<bottom> )\<longrightarrow> (\<rho> a x) \<close>


definition permission_dy::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where "permission_dy \<rho> \<sigma>  \<equiv> subordination \<rho> \<and> Top_con \<sigma> \<and> Bot \<sigma> \<and> SI_in \<sigma> \<and> WO_in \<sigma> \<and> OR_in \<rho> \<sigma> \<and> AND_in \<rho> \<sigma> "



(*The expriment here shows a modal translation for static permission, it is different from the one in the paper*)


(*Modal translation for (OR)\<^sup>-\<^sup>1 dynamic permissiomn*)
lemma thsubancon10: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall> a b x.  (\<rho> a x \<and>  \<sigma> (a\<^bold>\<or>b)(\<^bold>\<midarrow>x) ) \<longrightarrow> \<sigma> b(\<^bold>\<midarrow>x) ) \<longrightarrow> (\<exists>b. \<forall>a.( \<^bold>\<midarrow> (\<sigma> \<^bold>\<rhd> b)  \<^bold>\<preceq> \<^bold>\<midarrow> (\<rho> \<^bold>\<diamond> a ) ) )  ) " 
unfolding subordination_def and precontact 
  by (metis (mono_tags, lifting) BA_cp Bot_con_def precon_diamond_def subset_def supremum_def top_def)

lemma thsubancon11: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
(  (\<forall>b. \<exists>a.\<not> ( \<^bold>\<midarrow> (\<sigma> \<^bold>\<rhd> b)  \<^bold>\<preceq> \<^bold>\<midarrow> (\<rho> \<^bold>\<diamond> a ) ) ) \<longrightarrow>    (\<forall> a b x.  (\<rho> a x \<and>  \<sigma> (a\<^bold>\<or>b)(\<^bold>\<midarrow>x) ) \<longrightarrow> \<sigma> b(\<^bold>\<midarrow>x) )  ) " 
unfolding subordination_def and precontact   
  by (metis (mono_tags, lifting) BA_cp Bot_con_def precon_diamond_def subset_def supremum_def top_def) 

(*Modal translation for  (AND)\<^sup>-\<^sup>1 dynamic permission*)
lemma thsubancon12: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall> a b c.  (\<rho> a b \<and>  \<sigma> a (\<^bold>\<midarrow>(b\<^bold>\<and>c)) ) \<longrightarrow> \<sigma> a (\<^bold>\<midarrow>c) ) \<longrightarrow> (\<forall>a. \<exists>b. ( (\<rho> \<^bold>\<diamond> a ) \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> b  ) )  ) " 
unfolding subordination_def and precontact SB_con_def precon_diamond_def sup_char   
  by (metis sup_char)

lemma thsubancon13: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall>a. \<exists>b.\<not> ( (\<rho> \<^bold>\<diamond> a ) \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> b  ) )  ) \<longrightarrow> (\<forall> a b c.  (\<rho> a b \<and>  \<sigma> a (\<^bold>\<midarrow>(b\<^bold>\<and>c)) ) \<longrightarrow> \<sigma> a (\<^bold>\<midarrow>c) ) " 
unfolding subordination_def and precontact   subset_def infimum_def slanted_diamond_def  
  by (metis Bot_def bottom_def)

(*Modal translation for (CT)\<^sup>-\<^sup>1 dynamic permission *)
lemma thsubancon14: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
( (\<forall> a x y.  (\<rho> a x \<and> \<sigma> a(\<^bold>\<midarrow>(x\<^bold>\<and>y)) ) \<longrightarrow>  \<sigma> (a\<^bold>\<and>x)(\<^bold>\<midarrow>y) ) \<longrightarrow> (   \<exists>b.  \<forall>a. (\<sigma> \<^bold>\<rhd> a)  \<^bold>\<preceq> (\<rho> \<^bold>\<box> (\<sigma> \<^bold>\<rhd> b) ) )  ) "  
unfolding subordination_def and precontact 
  by (metis precontact subordination_def thsubancon8 thsubancon9)

lemma thsubancon15: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
(  (\<forall>b.  \<exists>a.\<not> ((\<sigma> \<^bold>\<rhd> a)  \<^bold>\<preceq> (\<rho> \<^bold>\<box> (\<sigma> \<^bold>\<rhd> b)) ) )  ) \<longrightarrow> (\<forall> a x y.  (\<rho> a x \<and> \<sigma> a(\<^bold>\<midarrow>(x\<^bold>\<and>y)) ) \<longrightarrow>  \<sigma> (a\<^bold>\<and>x)(\<^bold>\<midarrow>y) ) "  
unfolding subordination_def and precontact 
  by (metis precontact subordination_def thsubancon8 thsubancon9)

(*More expriment based on the intial formoulation of Makinson and van der Torre*)
definition Q5::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>Q5 \<rho> \<equiv> \<forall> a b. (\<rho> a b) \<longrightarrow> (a \<^bold>\<preceq> b) \<close>
 
lemma contraposition: "precontact \<rho> \<longrightarrow> S6 \<rho>" unfolding precontact  nitpick oops
lemma subtocon0:  "(subordination \<rho> \<and> S6 \<rho> \<and> Q5 \<rho>)  \<longrightarrow>   precontact \<rho>"  nitpick oops
lemma subtocon1:  "(subordination \<rho> \<and> S6 \<rho> \<and> Q5 \<rho>)  \<longrightarrow>   SI_in \<rho>"  nitpick oops
lemma subtocon2:  "(subordination \<rho> \<and> S6 \<rho> \<and> Q5 \<rho>)  \<longrightarrow>   WO_in \<rho>" by (simp add: WO_def WO_in_def subordination_def)
lemma subtocon3:  "(subordination \<rho> \<and> S6 \<rho> \<and> Q5 \<rho>)  \<longrightarrow>   AND_con \<rho>" nitpick oops
lemma subtocon4:  "(subordination \<rho> \<and> S6 \<rho> \<and> Q5 \<rho>)  \<longrightarrow>   OR_con \<rho>" unfolding OR_def and  SI_def 
  by (metis L3 OR_con_def SI_def subordination_def)
  
lemma subORcon: " (subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> OR_in \<rho> \<sigma> " unfolding subordination_def 
  by (metis OR_def OR_in_def subordination_def)

lemma subSIcon: " (subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> SI_in \<sigma> " unfolding subordination_def 
  by (metis (no_types, opaque_lifting) BA_dn SI_def SI_in_def)

lemma subWOcon: " (subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> WO_in \<sigma> " unfolding subordination_def  
  by (metis WO_con_def WO_in_def subordination_def subtoconwo)
 
lemma subTopcon: " (subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> Top_in \<sigma> " unfolding subordination_def  
  by (metis Bot_con_def Top_in_def precontact subordination_def subtoconth)

lemma subBotcon: " (subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> Bot_in \<sigma> " unfolding subordination_def 
  by (metis Bot_in_def Top_con_def subordination_def subtocontop)

lemma subANDcon: " (subordination \<rho>  \<and>  (\<forall> a x. \<rho> a x \<longleftrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) )) \<longrightarrow> AND_in \<rho> \<sigma> " unfolding subordination_def 
  by (metis AND_def AND_in_def subordination_def)

lemma subricon: "( subordination \<rho> \<and> precontact \<sigma> \<and>  CS1 \<rho> \<sigma> \<and>  CS2 \<rho> \<sigma>) \<longrightarrow> (\<forall> a x. \<rho> a x \<longrightarrow> \<not>(\<sigma> a(\<^bold>\<midarrow>x)) ) " unfolding CS2_def precontact  
(*  sledgehammer ( BA_deMorgan1 BA_dn L10 L14 SI_in_def compl_def join_def setequ_equ subset_def top_def)*) oops


(*
definition C11::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>C11 \<rho> \<equiv> \<not> (\<rho> \<^bold>\<top> \<^bold>\<bottom>)\<close>
definition C12::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>C12 \<rho> \<equiv> \<not> (\<rho> \<^bold>\<bottom> \<^bold>\<top>)\<close>
definition C2::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>C2 \<rho> \<equiv> \<forall> a x y. (\<rho> a (x\<^bold>\<or>y)) \<longrightarrow> ((\<rho> a x) \<or> (\<rho> a y))\<close>
definition C2'::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" where \<open>C2' \<rho> \<equiv> \<forall> a b x. (\<rho> (a\<^bold>\<or>b) x) \<longrightarrow> ((\<rho> a x) \<or> (\<rho> b x))\<close>
definition contact_def : "contact \<rho> \<equiv> C11 \<rho> \<and> C12 \<rho> \<and> C2 \<rho> \<and> C2' \<rho> \<and> SI_in \<rho> \<and> WO_in \<rho>"*)




end