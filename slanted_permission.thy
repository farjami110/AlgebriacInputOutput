theory slanted_permission
  imports contact_algebra

begin

declare[[show_types=false]] (*switch this on/off to see the actual types (useful to debug polymorphism problems)*)

(*Slanted operators*)
definition precon_diamond::" ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> 'w \<sigma>  \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<rhd>" 51) 
  where " \<rho> \<^bold>\<rhd> a  \<equiv> \<^bold>\<Or> (\<lambda>x.\<not> (\<rho> a x)) "  
definition precon_box::" ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> 'w \<sigma>  \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<unrhd>" 51) 
  where " \<rho> \<^bold>\<unrhd> a  \<equiv> \<^bold>\<Or> (\<lambda>x.\<not> (\<rho> x a))" 



(*Bi-subordination Algebra*)

(*Proposition 5.5 Item 1*)
lemma ainclubi1: "(subordination \<rho> \<and> subordination \<sigma> \<and> (\<forall> x y. \<rho> x y \<longrightarrow> \<sigma> x y ) ) \<longrightarrow>  (\<forall>a.  \<sigma> \<^bold>\<diamond> a \<^bold>\<preceq>  \<rho> \<^bold>\<diamond> a)"  
  by (simp add: inf_char slanted_diamond_def)
  
(*Proposition 5.5 Item 2*)
lemma subtomat: "subordination \<rho> \<and> subordination \<sigma> \<and> (\<forall> x y z .  (\<sigma> x z \<and> \<rho> z y )  \<longrightarrow>  x \<^bold>\<preceq> y  ) \<longrightarrow>   (\<forall> a.  \<rho> \<^bold>\<box> a \<^bold>\<preceq> \<sigma> \<^bold>\<diamond> a) " oops (* It needs more to try*)

(*Proposition 5.5 Item 7*)
lemma thsubancon16: "(subordination \<rho> \<and> subordination \<sigma>) \<longrightarrow> 
  (\<forall> b. ((\<forall> a. (\<rho> a b)) \<longrightarrow> (\<forall>a. (\<sigma> a b)) )) \<longrightarrow>   ((\<sigma> \<^bold>\<diamond> \<^bold>\<top>)  \<^bold>\<preceq> (\<rho> \<^bold>\<diamond>\<^bold>\<top>) )"  
  unfolding subordination_def  SI_def inf_char subset_def top_def
  by (smt (z3) inf_char slanted_diamond_def subset_def)

(*Proposition 5.5 Item 6*)
lemma thsubancon19: " (subordination \<rho> \<and> subordination \<sigma>) \<longrightarrow> 
  (\<forall> a. (\<forall> b. ( (\<rho> a b) \<longrightarrow>  ( \<sigma> a b))  \<longrightarrow>   (b \<^bold>\<preceq> \<^bold>\<top>)\<and> (\<^bold>\<top> \<^bold>\<preceq> b)) \<longrightarrow>  ( \<^bold>\<top>  \<^bold>\<preceq> (\<sigma> \<^bold>\<diamond> a)\<^bold>\<or>(\<rho> \<^bold>\<diamond> a)))  " 
  unfolding subordination_def 
  by (metis L3 antisymmetric_def inf_char slanted_diamond_def subset_antisymmetric)

lemma thsubancon23: " (subordination \<rho> \<and> subordination \<sigma>) \<longrightarrow> 
  ( (\<forall> a. (\<exists> b. ((\<rho> a b) \<and> (\<sigma> b \<^bold>\<bottom>)) \<longrightarrow> (a \<^bold>\<preceq> \<^bold>\<bottom>)) ) \<longrightarrow>  ((\<rho> \<^bold>\<box> (\<sigma> \<^bold>\<box> \<^bold>\<bottom>)) \<^bold>\<preceq> \<^bold>\<bottom>) )" 
  unfolding subordination_def oops (*It needs more to try*)


(*Subordination + Precontact Algebras*)
lemma subconth1: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> x y. \<rho> x y \<longrightarrow> \<sigma> x y) \<longrightarrow>  (\<forall> a. \<not> ( \<rho> \<^bold>\<diamond> a \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> a))   ) " unfolding subordination_def  
  by (metis Bot_con_def SI_def Top_def bottom_def precontact subset_def)

lemma subconth2: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> x y. \<sigma> x y \<longrightarrow> \<rho> x y) \<longrightarrow> (\<forall> x y.\<not> (y \<^bold>\<preceq>  \<sigma> \<^bold>\<rhd> x) \<longrightarrow> (\<rho> \<^bold>\<diamond> x \<^bold>\<preceq> y ))  ) " 
  unfolding subordination_def and precontact inf_char precon_diamond_def slanted_diamond_def sup_char by (metis inf_char sup_char)

lemma subconth3: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> x y. \<rho> x y \<longrightarrow> \<not> (\<sigma> x (\<^bold>\<midarrow>y))) \<longrightarrow> (\<forall>a. (\<^bold>\<midarrow>(\<sigma> \<^bold>\<rhd> a)) \<^bold>\<preceq>  \<rho> \<^bold>\<diamond> a  )  ) " 
unfolding subordination_def and precontact inf_char precon_diamond_def slanted_diamond_def sup_char 
  by (metis dom_compl_def iDM_b inf_char setequ_equ)

lemma subconth4: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> x y. \<not> (\<sigma> x (\<^bold>\<midarrow>y)) \<longrightarrow> \<rho> x y ) \<longrightarrow> (\<forall>a.  \<rho> \<^bold>\<diamond> a  \<^bold>\<preceq>  (\<^bold>\<midarrow>(\<sigma> \<^bold>\<rhd> a))  )  ) " 
  unfolding subordination_def and precontact inf_char precon_diamond_def slanted_diamond_def sup_char 
  by (smt (verit) dom_compl_def iDM_b infimum_def setequ_equ subset_def)

lemma subconth5: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> x y. \<sigma> x y \<longrightarrow> \<not> (\<rho> x (\<^bold>\<midarrow>y))) \<longrightarrow> (\<forall>a. (\<^bold>\<midarrow>(\<rho> \<^bold>\<diamond> a)) \<^bold>\<preceq>   \<sigma> \<^bold>\<rhd> a ) ) " 
unfolding subordination_def and precontact inf_char precon_diamond_def slanted_diamond_def sup_char 
  by (metis dom_compl_def iDM_a setequ_equ sup_char)

lemma subconth6: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> x y. \<not> (\<rho> x (\<^bold>\<midarrow>y)) \<longrightarrow> \<sigma> x y )\<longrightarrow> (\<forall>a.   \<sigma> \<^bold>\<rhd> a  \<^bold>\<preceq>  (\<^bold>\<midarrow>(\<rho> \<^bold>\<diamond> a)) )  ) " 
  unfolding subordination_def and precontact inf_char precon_diamond_def slanted_diamond_def sup_char 
  by (metis dom_compl_def iDM_a setequ_equ sup_char)

lemma subconth6a: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> (  (\<forall>a.   \<sigma> \<^bold>\<rhd> a  \<^bold>\<preceq>  (\<^bold>\<midarrow>(\<rho> \<^bold>\<diamond> a)) ) \<longrightarrow>  (\<forall> x y. \<not> (\<rho> x (\<^bold>\<midarrow>y)) \<longrightarrow> \<sigma> x y ) ) " 
    unfolding precon_diamond_def    oops


lemma thsubancon1: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> a c.  (\<exists> b. \<rho> a b \<and> \<sigma> b c  ) \<longrightarrow> \<sigma> a c ) \<longrightarrow> (\<forall>a. \<rho> \<^bold>\<box> (\<sigma> \<^bold>\<rhd> a)  \<^bold>\<preceq>  (\<sigma> \<^bold>\<rhd> a) )  ) " 
  unfolding subordination_def and precontact 
  by (smt (verit, best) Bot_con_def Bot_def WO_def bottom_def precon_diamond_def subset_def supremum_def top_def)
 
lemma thsubancon2: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> a b c.  (\<rho> a b \<and> \<sigma> a c  ) \<longrightarrow> \<sigma> a (b\<^bold>\<and>c) ) \<longrightarrow> (\<forall>a. \<exists>b. ( \<rho> \<^bold>\<box> (\<sigma> \<^bold>\<rhd> \<rho> \<^bold>\<diamond> a ) \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> b  ) )  ) " 
  unfolding subordination_def and precontact 
  by (metis (mono_tags, lifting) Bot_con_def precon_diamond_def subset_def sup_char top_def)

lemma thsubancon3: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> ( (\<forall> a b c.  (\<rho> a b \<and> \<sigma> a c  ) \<longrightarrow> \<sigma> a (b\<^bold>\<and>c) ) \<longrightarrow> (\<forall>a. \<exists>b. ( (\<sigma> \<^bold>\<rhd> \<rho> \<^bold>\<diamond> a ) \<^bold>\<preceq> \<sigma> \<^bold>\<rhd> b  ) )  ) " 
  unfolding subordination_def and precontact 
  by (metis setequ_def setequ_equ)

lemma thsubancon17: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
  (\<forall> a. ((\<forall> b. (\<rho> a b)) \<longrightarrow> (\<forall>b. (\<not> \<sigma> b a)) )) \<longrightarrow>   ((\<rho> \<^bold>\<box> \<^bold>\<bottom>)  \<^bold>\<preceq> (\<sigma> \<^bold>\<rhd>\<^bold>\<top>) )   " 
 unfolding subordination_def slanted_box_def precon_diamond_def  
  by (metis (mono_tags, lifting) WO_def bottom_def subset_def sup_char)

lemma thsubancon21: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
  (\<forall> a. \<forall>c. (\<forall> b. ( (\<rho> b c) \<longrightarrow>  (\<not> \<sigma> a b))) \<longrightarrow>  ((\<rho> \<^bold>\<box> c)   \<^bold>\<preceq> (\<sigma> \<^bold>\<rhd> a)))  " 
  unfolding subordination_def and precontact 
  by (simp add: precon_diamond_def slanted_box_def sup_char)

lemma thsubancon22: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
  (\<forall> a. (\<exists> b. ( (\<rho> a b) \<and>  (\<not> \<sigma> a b))) \<longrightarrow>  ((\<rho> \<^bold>\<diamond> a) \<^bold>\<preceq> (\<sigma> \<^bold>\<rhd> a)))  " 
  unfolding subordination_def and precontact  
  by (smt (verit) le31it1a precon_diamond_def subset_def supremum_def)

lemma thsubancon24: " (subordination \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
  ( (\<forall> a. (\<exists> b. ((\<rho> a b) \<and> (\<not> \<sigma> b \<^bold>\<bottom>)) \<longrightarrow> (a \<^bold>\<preceq> \<^bold>\<bottom>)) ) \<longrightarrow>  ((\<rho> \<^bold>\<box> (\<sigma> \<^bold>\<unrhd> \<^bold>\<top> )) \<^bold>\<preceq> \<^bold>\<bottom>) )" 
  unfolding subordination_def oops (*It needs more to try*)


(*Bi-precontact Algebra*)
lemma thsubancon18: " (precontact \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
  (\<forall> a.\<forall> b. (\<rho> a b  \<longrightarrow>   \<sigma> a b)) \<longrightarrow>   ((\<sigma> \<^bold>\<rhd> a)  \<^bold>\<preceq> (\<rho> \<^bold>\<rhd> a ) )   " 
unfolding precontact precon_diamond_def  
  by (metis sup_char)

lemma thsubancon20: " (precontact \<rho> \<and> precontact \<sigma>) \<longrightarrow> 
  (\<forall> a. (\<forall> b. ( (\<not> \<rho> a b) \<and>  (\<not> \<sigma> a b))  \<longrightarrow>   (b \<^bold>\<preceq> \<^bold>\<bottom>)) \<longrightarrow>  ( (\<sigma> \<^bold>\<rhd> a)\<^bold>\<and>(\<rho> \<^bold>\<rhd> a))  \<^bold>\<preceq> \<^bold>\<bottom> )  " 
  unfolding precontact  subset_def meet_def and  precon_diamond_def oops

 

(*More defintions*)
definition subrelation::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> bool" 
  where "subrelation \<rho> \<sigma> \<equiv>   \<forall> a x. \<rho> a x \<longrightarrow> \<sigma> a x"

definition sub_closure::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho>" 
  where "sub_closure \<rho>  \<equiv>  \<lambda>x y. \<forall>\<sigma>. subordination \<sigma> \<longrightarrow> (subrelation \<rho> \<sigma> \<longrightarrow> \<sigma> x y)"

definition con_closure::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho>" 
  where "con_closure \<rho>  \<equiv>  \<lambda>x y. \<forall>\<sigma>. precontact \<sigma> \<longrightarrow> (subrelation \<rho> \<sigma> \<longrightarrow> \<sigma> x y)"


(*
definition sub_closure::"('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<rho>" 
  where "sub_closure \<rho>  \<equiv> \<exists> \<sigma>. subordination \<sigma>  \<and> (\<forall> a x. \<rho> a x \<longrightarrow> \<sigma> a x)\<and> 
(\<forall>\<tau>. subordination \<tau> \<and> (\<forall> a x. \<rho> a x \<longrightarrow> \<tau> a x) \<longrightarrow> \<sigma> \<sqsubseteq> \<tau>) "
*)


end