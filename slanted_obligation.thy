theory slanted_obligation
  imports subordination_algebra

begin

declare[[show_types=false]] (*switch this on/off to see the actual types (useful to debug polymorphism problems)*)

(*Slanted operators*)
definition slanted_diamond::" ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> 'w \<sigma>  \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<diamond>" 51) 
  where " \<rho> \<^bold>\<diamond> a  \<equiv> \<^bold>\<And> (\<lambda>x. \<rho> a x)"  
definition slanted_box::" ('w \<sigma>,'w \<sigma>)\<rho> \<Rightarrow> 'w \<sigma>  \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<box>" 51) 
  where " \<rho> \<^bold>\<box> a  \<equiv> \<^bold>\<Or> (\<lambda>x. \<rho> x a)" 



(*Lemma 4.2*)
(*item 1(i)*)
lemma le31it1a: "\<rho> a x \<longrightarrow> (\<rho> \<^bold>\<diamond> a  \<^bold>\<preceq> x) " unfolding slanted_diamond_def  by (simp add: inf_char)
lemma le31it1b: "\<rho> a x \<longrightarrow> (a \<^bold>\<preceq> \<rho> \<^bold>\<box> x )" unfolding slanted_box_def by (simp add: sup_char)

(*item 1(ii-LtoR)*)
lemma le31it2: "WO \<rho> \<and> DD \<rho> \<longrightarrow> (\<forall>a x. (\<rho> a x \<longrightarrow> (\<rho> \<^bold>\<diamond> a  \<^bold>\<preceq> x)))" unfolding slanted_diamond_def by (simp add: inf_char)

(*While the  left to right is easy right to left is challenging *)
(*David: we can use nitpick to debug the problem, moreover ...*)
lemma recall_that: "\<^bold>\<And>(\<lambda>x. False) = \<^bold>\<top>" by (simp add: infimum_def top_def) 
lemma toptoall: " (\<forall>x. \<rho> x \<^bold>\<top>) \<longrightarrow> (\<forall>x. \<exists>y.  \<rho> x y)"  unfolding Top_def   by auto

(*item 1(ii-RtoL)*)
lemma "(WO \<rho> \<and> DD \<rho> \<and> SF \<rho> ) \<longrightarrow>(\<forall> x y. ((\<rho> \<^bold>\<diamond> y)  \<^bold>\<preceq> x)  \<longrightarrow> \<rho> y x)" 
  unfolding  slanted_diamond_def WO_def DD_def SF_def  oops (*needs to try more*)

lemma iitop1: "(WO \<rho> \<and> DD \<rho> \<and> (\<forall>x. \<rho> x \<^bold>\<top>) ) \<longrightarrow>( ((\<rho> \<^bold>\<diamond> \<^bold>\<top> )  \<^bold>\<preceq> \<^bold>\<top> )  \<longrightarrow> \<rho> \<^bold>\<top> \<^bold>\<top> )" 
  unfolding slanted_diamond_def by auto
lemma iitop2: "(WO \<rho> \<and> DD \<rho> \<and> (\<forall>x. \<rho> x \<^bold>\<top>) ) \<longrightarrow> ( ((\<rho> \<^bold>\<diamond> \<^bold>\<top> )  \<^bold>\<preceq> \<^bold>\<bottom> )  \<longrightarrow> \<rho> \<^bold>\<top> \<^bold>\<bottom> )" 
  unfolding WO_def DD_def slanted_diamond_def oops
(*nitpick[card 'a=1, eval="\<rho> \<^bold>\<diamond> y = \<^bold>\<top>"] oops  (*observe that (\<lambda>x. \<rho> y x) is empty*)*)

    
(*item 1(iii)*)
lemma "SI \<rho> \<and> UD \<rho> \<longrightarrow> (\<forall>a x. \<rho> a x \<longrightarrow> (a \<^bold>\<preceq> \<rho> \<^bold>\<box> x ))" unfolding slanted_box_def by (meson sup_char)
lemma "(SI \<rho> \<and> UD \<rho> \<and> SB \<rho>) \<longrightarrow> (\<forall>a x. (a \<^bold>\<preceq> \<rho> \<^bold>\<box> x )  \<longrightarrow>  \<rho> a x )" 
  unfolding SI_def UD_def  slanted_box_def  SB_def subset_def  oops  (*needs to try more*)



(*Lemma 4.4*)
(*item 7*)
lemma SIMON: "SI \<rho> \<longrightarrow> (x\<^bold>\<preceq>y \<longrightarrow>  ((\<rho> \<^bold>\<diamond> x)  \<^bold>\<preceq>  (\<rho> \<^bold>\<diamond> y)))" unfolding SI_def and slanted_diamond_def  by (metis inf_char)
(*item 8*)
lemma "WO \<rho> \<longrightarrow> (\<forall> x y.  x\<^bold>\<preceq>y \<longrightarrow>  ((\<rho> \<^bold>\<box> x)  \<^bold>\<preceq>  (\<rho> \<^bold>\<box> y)))" unfolding WO_def and slanted_box_def by (metis sup_char)



(*Lemma 4.5*)
(*item 1(i)*)
lemma "(WO \<rho> \<and> DD \<rho> \<and> (\<forall>x. \<rho> x \<^bold>\<top>) ) \<longrightarrow> ( (\<forall>x y. (x\<^bold>\<preceq>y \<longrightarrow>  ((\<rho> \<^bold>\<diamond> x)  \<^bold>\<preceq>  (\<rho> \<^bold>\<diamond> y))) ) \<longrightarrow> SI \<rho>)" 
 unfolding WO_def and DD_def and  SI_def and slanted_diamond_def SF_def oops (*needs to try more*)
(*item 1(ii)*)
lemma "(WO \<rho> \<and> OR \<rho> \<and> DD \<rho>) \<longrightarrow>  (\<forall>a b. (\<rho> \<^bold>\<diamond> (a \<^bold>\<or> b)) \<^bold>\<preceq> ((\<rho> \<^bold>\<diamond> a) \<^bold>\<or> (\<rho> \<^bold>\<diamond> b)))" 
  unfolding WO_def and OR_def and DD_def and slanted_diamond_def oops (*needs to try more*)
lemma "(WO \<rho> \<and> DD \<rho>) 
\<longrightarrow>  ( (\<forall>a b. (\<rho> \<^bold>\<diamond> (a \<^bold>\<or> b)) \<^bold>\<preceq> ((\<rho> \<^bold>\<diamond> a) \<^bold>\<or> (\<rho> \<^bold>\<diamond> b))) \<longrightarrow> OR \<rho>)" 
  unfolding WO_def and DD_def and  OR_def and slanted_diamond_def oops (*needs to try more ?*)
(*item 1(iii)*)
lemma "Bot \<rho> \<longrightarrow>  \<rho> \<^bold>\<diamond> \<^bold>\<bottom> \<^bold>\<preceq> \<^bold>\<bottom>"  unfolding Bot_def and slanted_diamond_def by (simp add: inf_char) 

(*item 2(i)*)
lemma "(SI \<rho> \<and> UD \<rho> \<and> SB \<rho> )  \<longrightarrow> ((\<forall>x y. (x\<^bold>\<preceq>y \<longrightarrow>  ((\<rho> \<^bold>\<box> x)  \<^bold>\<preceq>  (\<rho> \<^bold>\<box> y)))) \<longrightarrow> WO \<rho>)" 
  unfolding SI_def and UD_def and slanted_box_def and WO_def   oops (* need to try more*)
(*item 2(ii)*)
lemma "(SI \<rho> \<and>  AND \<rho> \<and> UD \<rho>  \<and> (\<forall>x. \<rho> \<^bold>\<bottom> x)  )  \<longrightarrow> (\<forall>a b. ( ((\<rho> \<^bold>\<box> a) \<^bold>\<and> (\<rho> \<^bold>\<box> b)) \<^bold>\<preceq> \<rho> \<^bold>\<box> (a \<^bold>\<and> b)) )" 
  unfolding  Bot_def  using  slanted_box_def sup_char supremum_def subset_def meet_def    oops  (*needs to try more*)
(*
SI_def and AND_def and UD_def and  supremum_def  slanted_box_def and subset_def  (* sledgehammer[verbose, timeout=180 ]*) oops (*needs to try more*) *)
lemma "(SI \<rho> \<and> UD \<rho> \<and> SB \<rho> ) \<longrightarrow> ((\<forall> a b. ((\<rho> \<^bold>\<box> a) \<^bold>\<and> (\<rho> \<^bold>\<box> b)) \<^bold>\<preceq> \<rho> \<^bold>\<box> (a \<^bold>\<and> b))\<longrightarrow> AND \<rho> )" 
  unfolding SI_def and UD_def and slanted_box_def and AND_def   oops (*needs to try more*)
(*item 2(iii)*)
lemma "Top \<rho> \<longrightarrow> \<^bold>\<top>  \<^bold>\<preceq> \<rho> \<^bold>\<box> \<^bold>\<top>" unfolding Top_def and slanted_box_def by (simp add: sup_char)
lemma " (SI \<rho> \<and> UD \<rho> \<and> SB \<rho> ) \<longrightarrow>((\<^bold>\<top>  \<^bold>\<preceq> \<rho> \<^bold>\<box> \<^bold>\<top>) \<longrightarrow> Top \<rho>)" 
  unfolding SI_def and UD_def and Top_def and slanted_box_def  oops  (*needs to try more*)
 


(*lemma 4.7*)
(*item 1(i)*)
lemma "(SI \<rho> \<and> WO \<rho> \<and> DD \<rho> \<and> SF \<rho>) \<longrightarrow> down_directed (\<lambda>x. \<exists> y. \<rho> x y)"  by (metis SF_def down_directed_def inf_ext)
lemma "((SI \<rho> \<and> WO \<rho> \<and> DD \<rho> \<and> SF \<rho>)\<and> down_directed D1) \<longrightarrow> (down_directed (\<lambda>x. (\<exists> y. (D1 y  \<and> \<rho> x y))) )"  
  by (smt (verit, ccfv_threshold) SI_def down_directed_def inf_char)

(*item 1(ii)*)
lemma "((Extension B A) \<and> (SI \<rho> \<and> WO \<rho> \<and> DD \<rho> \<and> SF \<rho>) \<and> down_directed D1) \<longrightarrow> ((closed(\<^bold>\<And>(\<lambda>x. \<exists> y. D1 y \<and> \<rho> x y)) A B))" oops (*needs to try more*)

(*item 1(iii)*)
lemma "((Extension B A \<and> closed cl A B \<and>  (\<rho> \<^bold>\<diamond> cl) \<^bold>\<preceq> b ) \<and> B b) \<longrightarrow> (SI \<rho> \<and> WO \<rho> \<and> DD \<rho> \<and> SF \<rho>)
 \<longrightarrow> (\<exists> a. \<rho> a b \<and> cl \<^bold>\<preceq> a \<and> B a )" unfolding Extension_def closed_def  oops (*needs to try more*)

(*item 1(iv)*)
lemma " ((Extension B A \<and> closed cl A B \<and> open op A B \<and>  (\<rho> \<^bold>\<diamond> cl) \<^bold>\<preceq> op ) ) \<longrightarrow> (SI \<rho> \<and> WO \<rho> \<and> DD \<rho> \<and> SF \<rho>)
 \<longrightarrow> (\<exists> a b. \<rho> a b \<and> cl \<^bold>\<preceq> a \<and> b \<^bold>\<preceq> op)"  oops (*needs to try more*)

(*item 2(i)*)
lemma "((SI \<rho> \<and> WO \<rho> \<and> UD \<rho> \<and> SB \<rho>)\<and> up_directed U1) \<longrightarrow> (up_directed (\<lambda>x. (\<exists> y. (U1 y  \<and> \<rho> y x))) )" 
  unfolding  WO_def up_directed_def using subset_def by blast
   
   
  

(*Proposition 5.1*)
(*item 1(i)*)
lemma "(\<forall>x y. (\<rho> x y \<longrightarrow> x \<^bold>\<preceq> y)) \<longrightarrow> (\<forall> a. a \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> a))" unfolding slanted_diamond_def by (simp add: inf_char) 

(*item 1(iii)*)
lemma "SI \<rho> \<longrightarrow> (CT \<rho> \<longrightarrow> T \<rho>)" unfolding SI_def and CT_def and T_def  by (metis L3 L5)
lemma "(WO \<rho> \<and> DD \<rho> \<and> SI \<rho>) \<longrightarrow> (T \<rho>  \<longrightarrow>  (\<forall>a. (\<rho> \<^bold>\<diamond> a) \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> (\<rho> \<^bold>\<diamond> a))) )"
  unfolding WO_def and DD_def and SI_def and T_def and slanted_diamond_def and subset_def oops (*needs to try more*)
lemma "WO \<rho> \<and> DD \<rho> \<and> SI \<rho>  \<longrightarrow> ( (\<forall>a. (\<rho> \<^bold>\<diamond> a) \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> (\<rho> \<^bold>\<diamond> a))) \<longrightarrow> T \<rho>)" 
  unfolding WO_def and DD_def and SI_def and T_def and slanted_diamond_def  oops  (*needs to try more *)

(*item 1(iv)*)
lemma "WO \<rho> \<and> DD \<rho> \<and> SI \<rho>  \<longrightarrow> (D \<rho>  \<longrightarrow>  (\<forall>a.(\<rho> \<^bold>\<diamond> (\<rho> \<^bold>\<diamond> a)) \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> a) ) )"
  unfolding WO_def and DD_def and SI_def and D_def and slanted_diamond_def   by (smt (verit, del_insts) inf_char)
lemma "(WO \<rho> \<and> DD \<rho> \<and> SI \<rho> \<and> SF \<rho> ) \<longrightarrow>  ((\<forall>a. (\<rho> \<^bold>\<diamond> (\<rho> \<^bold>\<diamond> a)) \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> a)) \<longrightarrow> D \<rho>)"
  unfolding WO_def and DD_def and SI_def and D_def and slanted_diamond_def   oops (*needs to try more*)

(*item 2(i)*)
lemma "WO \<rho> \<and> DD \<rho> \<and> SI \<rho>  \<longrightarrow> (CT \<rho>  \<longrightarrow>  (\<forall>a. (\<rho> \<^bold>\<diamond> a) \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> (a\<^bold>\<and>(\<rho> \<^bold>\<diamond> a)))) )"
  unfolding WO_def  DD_def SI_def CT_def slanted_diamond_def subset_def meet_def supremum_def  oops (*needs to try more*)
lemma "WO \<rho> \<and> DD \<rho> \<and> SI \<rho>  \<longrightarrow> ( (\<forall>a. (\<rho> \<^bold>\<diamond> a) \<^bold>\<preceq> (\<rho> \<^bold>\<diamond> (a\<^bold>\<and>(\<rho> \<^bold>\<diamond> a)))) \<longrightarrow> CT \<rho> )"
  unfolding WO_def and DD_def and SI_def and CT_def and slanted_diamond_def oops  

(*item 4(i)*)
lemma "S6 \<rho> \<longrightarrow> (\<forall>a. (\<^bold>\<midarrow>(\<rho> \<^bold>\<diamond> a)) \<^bold>\<approx> (\<rho> \<^bold>\<box> \<^bold>\<midarrow> a ))" unfolding S6_def and slanted_diamond_def and slanted_box_def
  by (smt (z3) BA_dn dom_compl_char iDM_a setequ_char supremum_def)
lemma " ((\<forall>x. \<exists>y. \<rho> y x) \<and> (\<forall>z. \<exists>u. \<rho> z u))  \<longrightarrow>   ( (\<forall>a. ( (\<^bold>\<midarrow>(\<rho> \<^bold>\<diamond> a)) \<^bold>\<approx> (\<rho> \<^bold>\<box> \<^bold>\<midarrow> a )) )  \<longrightarrow> S6 \<rho>)" 
  unfolding S6_def and slanted_diamond_def and slanted_box_def nitpick  oops (*Why counter model?*)


end 

 