theory Chains
  imports Main 
begin

abbreviation emptySet (\<open>\<emptyset>\<close>) 
  where \<open>\<emptyset> \<equiv> {}\<close>

lemma conv_rel_pow_iff[iff]:
 fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and x y :: 'a
 shows \<open>(R\<inverse>\<inverse> ^^ n) x y \<longleftrightarrow> (R^^n) y x\<close>
proof (intro iffI)
  show G1: \<open>(R\<inverse>\<inverse> ^^ n) x y\<close> if as: \<open>(R^^n) y x\<close> 
    for R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and x y :: 'a
  using as proof (induct n arbitrary: x y)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then obtain z where \<open>(R^^n) y z\<close> \<open>R z x\<close> by auto
    then have A: \<open>(R\<inverse>\<inverse>^^n) z y\<close> using Suc by metis
    have \<open>R\<inverse>\<inverse> x z\<close> using \<open>R z x\<close> by auto
    then show ?case using A by (meson relpowp_Suc_I2)        
  qed
  show \<open>(R^^n) y x\<close> if as: \<open>(R\<inverse>\<inverse> ^^ n) x y\<close> 
    using G1[of \<open>R\<inverse>\<inverse>\<close>] as by simp
qed

lemma conv_rtranclp[simp]: \<open>R\<inverse>\<inverse>\<^sup>*\<^sup>* x y \<longleftrightarrow> R\<^sup>*\<^sup>* y x\<close>  
  by (meson rtranclp_converseD rtranclp_converseI)

lemma conv_tranclp[iff]: \<open>R\<inverse>\<inverse>\<^sup>+\<^sup>+ x y \<longleftrightarrow> R\<^sup>+\<^sup>+ y x\<close>  
  by (simp add: tranclp_converse)

lemma tranclp_conv[iff]: \<open>R\<^sup>+\<^sup>+\<inverse>\<inverse> x y \<longleftrightarrow> R\<^sup>+\<^sup>+ y x\<close>  
  by (simp add: tranclp_converse)

lemma conv_tranclp_eq[simp]: \<open>R\<inverse>\<inverse>\<^sup>+\<^sup>+ =  R\<^sup>+\<^sup>+\<inverse>\<inverse>\<close>
  by (intro ext ; simp)

lemma ex1_pair_eq: 
  assumes \<open>\<exists>!(a,b). P a b\<close> \<open>P a\<^sub>1 b\<^sub>1\<close> \<open>P a\<^sub>2 b\<^sub>2\<close>
  shows \<open>a\<^sub>1 = a\<^sub>2\<close> \<open>b\<^sub>1 = b\<^sub>2\<close> 
proof -
  obtain x where A: \<open>case x of (a, b) \<Rightarrow> P a b\<close> 
      and B: \<open>\<forall>y. (case y of (a, b) \<Rightarrow> P a b) \<longrightarrow> y = x\<close>
    using assms(1) by metis
  let ?y = \<open>(a\<^sub>1,b\<^sub>1)\<close> and ?z = \<open>(a\<^sub>2,b\<^sub>2)\<close>
  have C1: \<open>(a\<^sub>1, b\<^sub>1) = x\<close> 
    using B[rule_format,of \<open>(a\<^sub>1, b\<^sub>1)\<close>] \<open>P a\<^sub>1 b\<^sub>1\<close> 
    by (simp ; metis)
  have C2: \<open>(a\<^sub>2, b\<^sub>2) = x\<close> 
    using B[rule_format,of \<open>(a\<^sub>2, b\<^sub>2)\<close>] \<open>P a\<^sub>2 b\<^sub>2\<close> 
    by (simp ; metis)
  show \<open>a\<^sub>1 = a\<^sub>2\<close> \<open>b\<^sub>1 = b\<^sub>2\<close>
    using C1 C2 by auto
qed

lemma nat_set_min:
  fixes X :: \<open>nat set\<close>
  assumes \<open>X \<noteq> \<emptyset>\<close>
  obtains x where \<open>x \<in> X\<close> \<open>\<And>z. z \<in> X \<Longrightarrow> x \<le> z\<close>
  using assms
  by (metis (full_types) Collect_mem_eq empty_Collect_eq exists_least_iff not_le)

locale binary_relation =
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>

locale set_with_relation =
  binary_relation R 
  for R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> +
  fixes
    \<X> :: \<open>'a set\<close>


context binary_relation
begin

lemma R_conv_rtrancl[simp]: \<open>R\<inverse>\<inverse>\<^sup>*\<^sup>* x y = R\<^sup>*\<^sup>* y x\<close>
  by (meson rtranclp_converseD rtranclp_converseI)

definition \<open>is_upper_order_of n x \<equiv> \<exists>y. (R^^n) x y \<and> (\<forall>z. \<not> R y z)\<close>

definition \<open>is_upper_bound_of y x \<equiv> R\<^sup>*\<^sup>* x y \<and> (\<forall>z. \<not> R y z)\<close>

definition \<open>is_lower_order_of n x \<equiv> \<exists>y. (R^^n) y x \<and> (\<forall>z. \<not> R z y)\<close>

definition \<open>is_lower_bound_of y x \<equiv> R\<^sup>*\<^sup>* y x \<and> (\<forall>z. \<not> R z y)\<close>

definition \<open>upper_order x \<equiv> THE n. is_upper_order_of n x\<close>

definition \<open>upper_bound x \<equiv> THE y. is_upper_bound_of y x\<close>

definition \<open>lower_order x \<equiv> THE n. is_lower_order_of n x\<close>

definition \<open>lower_bound x \<equiv> THE y. is_lower_bound_of y x\<close>

end

locale non_empty_set_with_relation = 
  set_with_relation +
  assumes set_not_empty: \<open>\<X> \<noteq> \<emptyset>\<close>

locale chain = non_empty_set_with_relation +
  assumes
    R_connected:
      \<open>\<And>x y. \<lbrakk> x \<in> \<X> ; y \<in> \<X> \<rbrakk> \<Longrightarrow> R\<^sup>*\<^sup>* x y \<or> R\<^sup>*\<^sup>* y x\<close>
  
locale lb_chain = chain +
  assumes
    lb_exists: \<open>\<exists>x \<in> \<X>. \<forall>y \<in> \<X>. R\<^sup>*\<^sup>* x y\<close>

locale ub_chain = chain +
  assumes
    ub_exists: \<open>\<exists>x \<in> \<X>. \<forall>y \<in> \<X>. R\<^sup>*\<^sup>* y x\<close>

locale bchain = lb_chain + ub_chain

locale single_valued_range_relation =
  binary_relation +
  assumes
    single_valued_range: \<open>\<lbrakk> R x y ; R x z \<rbrakk> \<Longrightarrow> y = z\<close>

locale single_valued_domain_relation =
  binary_relation +
  assumes
    single_valued_domain: \<open>\<lbrakk> R y x ; R z x \<rbrakk> \<Longrightarrow> y = z\<close>

locale acyclic_relation =
  binary_relation +
  assumes
    acyclic: \<open>\<not> R\<^sup>+\<^sup>+ x x\<close>

locale single_valued_range_acyclic_relation =
  single_valued_range_relation + acyclic_relation

locale single_valued_domain_acyclic_relation =
  single_valued_domain_relation + acyclic_relation

locale upper_bounded_relation =
  binary_relation +
    assumes
      upper_bounded[intro!,simp]: \<open>\<exists>y. is_upper_bound_of y x\<close>

locale lower_bounded_relation =
  binary_relation +
    assumes
      lower_bounded[intro!,simp]: \<open>\<exists>y. is_lower_bound_of y x\<close>

locale single_valued_range_upper_bounded_relation =
  single_valued_range_relation + upper_bounded_relation

locale single_valued_domain_lower_bounded_relation =
  single_valued_domain_relation + lower_bounded_relation

locale wellfounded_relation =
  binary_relation +
    assumes
      wellfounded: \<open>wfP R\<close>

locale noetherian_relation =
  binary_relation +
    assumes
      noetherian: \<open>wfP R\<inverse>\<inverse>\<close>

locale single_valued_domain_wellfounded_relation =
  single_valued_domain_relation +
  wellfounded_relation

locale single_valued_range_noetherian_relation =
  single_valued_range_relation +
  noetherian_relation

locale finite_lb_chains_relation =
  binary_relation +  
  assumes finite_lb_chains: \<open>lb_chain R X \<Longrightarrow> finite X\<close>

locale finite_ub_chains_relation =
  binary_relation +  
  assumes finite_ub_chains: \<open>ub_chain R X \<Longrightarrow> finite X\<close>

locale single_valued_range_acyclic_finite_lb_chains_relation =
  single_valued_range_acyclic_relation +
  finite_lb_chains_relation


context binary_relation
begin

inductive_set R_Chains where
  \<open>chain R X  \<Longrightarrow> X \<in> R_Chains\<close>

inductive_set R_LB_Chains where
  \<open>lb_chain R X \<Longrightarrow> X \<in> R_LB_Chains\<close>

inductive_set R_UB_Chains where
  \<open>ub_chain R X \<Longrightarrow> X \<in> R_UB_Chains\<close>

inductive_set R_B_Chains where
  \<open>bchain R X \<Longrightarrow> X \<in> R_B_Chains\<close>

end

lemma conv_chains[iff]: \<open>chain (R\<inverse>\<inverse>) \<X> \<longleftrightarrow> chain R \<X>\<close>
  by (meson chain_def 
            chain_axioms_def rtranclp_converseD 
            rtranclp_converseI)

lemma conv_ub_chain[iff]: \<open>ub_chain (R\<inverse>\<inverse>) \<X> \<longleftrightarrow> lb_chain R \<X>\<close>  
  by (metis conv_chains conversep.simps lb_chain_axioms_def lb_chain_def
            rtranclp_conversep ub_chain.axioms(1) ub_chain.intro 
            ub_chain.ub_exists ub_chain_axioms_def)

lemma conv_lb_chain[iff]: \<open>lb_chain (R\<inverse>\<inverse>) \<X> \<longleftrightarrow> ub_chain R \<X>\<close>  
  by (metis conv_chains conversep.simps lb_chain_axioms_def lb_chain_def
            rtranclp_conversep ub_chain.axioms(1) ub_chain.intro 
            ub_chain.ub_exists ub_chain_axioms_def)

lemma conv_bchain[iff]: \<open>bchain (R\<inverse>\<inverse>) \<X> \<longleftrightarrow> bchain R \<X>\<close>    
  by (meson bchain_def conv_lb_chain conv_ub_chain)

lemma tranclp_chain[iff]: \<open>chain (R\<^sup>+\<^sup>+) \<X> \<longleftrightarrow> chain R \<X>\<close>  
  by (simp add: chain_def chain_axioms_def)

lemma tranclp_lb_chain[iff]: \<open>lb_chain (R\<^sup>+\<^sup>+) \<X> \<longleftrightarrow> lb_chain R \<X>\<close>    
  by (metis lb_chain.lb_exists lb_chain_axioms.intro lb_chain_def 
            tranclp_chain tranclp_rtranclp_absorb)

lemma tranclp_ub_chain[iff]: \<open>ub_chain (R\<^sup>+\<^sup>+) \<X> \<longleftrightarrow> ub_chain R \<X>\<close>  
  by (metis conv_lb_chain tranclp_converse tranclp_lb_chain)

lemma tranclp_bchain[iff]: \<open>bchain (R\<^sup>+\<^sup>+) \<X> \<longleftrightarrow> bchain R \<X>\<close>    
  by (simp add: bchain_def)

lemma rtranclp_chain[iff]: \<open>chain (R\<^sup>*\<^sup>*) \<X> \<longleftrightarrow> chain R \<X>\<close>      
  by (simp add: chain_def chain_axioms_def)

lemma rtranclp_lb_chain[iff]: \<open>lb_chain (R\<^sup>*\<^sup>*) \<X> \<longleftrightarrow> lb_chain R \<X>\<close>        
  by (simp add: lb_chain_axioms_def lb_chain_def)

lemma rtranclp_ub_chain[iff]: \<open>ub_chain (R\<^sup>*\<^sup>*) \<X> \<longleftrightarrow> ub_chain R \<X>\<close>        
  by (simp add: ub_chain_axioms_def ub_chain_def)

lemma rtranclp_bchain[iff]: \<open>bchain (R\<^sup>*\<^sup>*) \<X> \<longleftrightarrow> bchain R \<X>\<close>          
  by (simp add: bchain_def)

lemma (in binary_relation) is_upper_order_of_I[intro]:
  assumes \<open>(R^^n) x y\<close> \<open>\<And>z. \<not> R y z\<close>
  shows \<open>is_upper_order_of n x\<close>
  using assms by (auto simp: is_upper_order_of_def)

lemma (in binary_relation) is_upper_order_of_E[elim]:
  assumes \<open>is_upper_order_of n x\<close>
  obtains y where \<open>(R^^n) x y\<close> \<open>\<And>z. \<not> R y z\<close>
  using assms by (auto simp: is_upper_order_of_def)

lemma (in binary_relation) is_upper_bound_of_I[intro!]:
  assumes \<open>R\<^sup>*\<^sup>* x y\<close> \<open>\<And>z. \<not> R y z\<close>
  shows \<open>is_upper_bound_of y x\<close>
  using assms by (auto simp: is_upper_bound_of_def)

lemma (in binary_relation) is_upper_bound_of_E[elim!]:
  assumes \<open>is_upper_bound_of y x\<close>
  obtains \<open>R\<^sup>*\<^sup>* x y\<close> \<open>\<And>z. \<not> R y z\<close>
  using assms by (auto simp: is_upper_bound_of_def)


lemma (in binary_relation) is_lower_order_of_I[intro]:
  assumes \<open>(R^^n) y x\<close> \<open>\<And>z. \<not> R z y\<close>
  shows \<open>is_lower_order_of n x\<close>
  using assms by (auto simp: is_lower_order_of_def)

lemma (in binary_relation) is_lower_order_of_E[elim]:
  assumes \<open>is_lower_order_of n x\<close>
  obtains y where \<open>(R^^n) y x\<close> \<open>\<And>z. \<not> R z y\<close>
  using assms by (auto simp: is_lower_order_of_def)

lemma (in binary_relation) is_lower_bound_of_I[intro!]:
  assumes \<open>R\<^sup>*\<^sup>* y x\<close> \<open>\<And>z. \<not> R z y\<close>
  shows \<open>is_lower_bound_of y x\<close>
  using assms by (auto simp: is_lower_bound_of_def)

lemma (in binary_relation) is_lower_bound_of_E[elim!]:
  assumes \<open>is_lower_bound_of y x\<close>
  obtains \<open>R\<^sup>*\<^sup>* y x\<close> \<open>\<And>z. \<not> R z y\<close>
  using assms by (auto simp: is_lower_bound_of_def)

context binary_relation
begin

declare R_Chains.intros[intro!] 
        R_LB_Chains.intros[intro!]
        R_UB_Chains.intros[intro!]
        R_B_Chains.intros[intro!]

declare 
  R_Chains.cases[elim!]
  R_LB_Chains.cases[elim!]
  R_UB_Chains.cases[elim!]
  R_B_Chains.cases[elim!]

lemma R_Chain_iff[simp]: \<open>X \<in> R_Chains \<longleftrightarrow> chain R X\<close>
  by auto

lemma R_LB_Chain_iff[simp]: \<open>X \<in> R_LB_Chains \<longleftrightarrow> lb_chain R X\<close>
  by auto

lemma R_UB_Chain_iff[simp]: \<open>X \<in> R_UB_Chains \<longleftrightarrow> ub_chain R X\<close>
  by auto

lemma R_B_Chain_iff[simp]: \<open>X \<in> R_B_Chains \<longleftrightarrow> bchain R X\<close>
  by auto

lemma lb_chains_subset_chains: \<open>R_LB_Chains \<subseteq> R_Chains\<close>
  using lb_chain.axioms(1) by blast  

lemma ub_chains_subset_chains: \<open>R_UB_Chains \<subseteq> R_Chains\<close>
  using ub_chain.axioms(1) by blast  

lemma b_chains_subset_lb_chains: \<open>R_B_Chains \<subseteq> R_LB_Chains\<close>  
  using bchain.axioms(1) by auto  

lemma b_chains_subset_ub_chains: \<open>R_B_Chains \<subseteq> R_UB_Chains\<close>  
  using bchain.axioms(2) by auto  

lemma b_chains_subset_chains: \<open>R_B_Chains \<subseteq> R_Chains\<close>    
  using b_chains_subset_ub_chains ub_chains_subset_chains by auto  

end

lemma conv_single_valued_range_relation[iff]:
  \<open>single_valued_range_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
    single_valued_domain_relation R\<close>  
  by (metis conversep.intros conversepD single_valued_domain_relation_def
            single_valued_range_relation_def)

lemma conv_single_valued_domain_relation[iff]:
  \<open>single_valued_domain_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
    single_valued_range_relation R\<close>  
  by (metis conversep.intros conversepD single_valued_domain_relation_def
            single_valued_range_relation_def)

lemma conv_acyclic_relation[iff]:
  \<open>acyclic_relation (R\<inverse>\<inverse>) \<longleftrightarrow> acyclic_relation R\<close>  
  by (simp add: acyclic_relation_def tranclp_converse)

lemma tranclp_tranclp_iff[iff]:  \<open>R\<^sup>+\<^sup>+\<^sup>+\<^sup>+ x y \<longleftrightarrow> R\<^sup>+\<^sup>+ x y\<close>
  by (metis tranclp.simps tranclpD tranclp_rtranclp_absorb 
            tranclp_rtranclp_tranclp)

lemma tranclp_acyclic_relation[iff]:
  \<open>acyclic_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow> acyclic_relation R\<close>  
  by (simp add: acyclic_relation_def)

lemma conv_single_valued_range_acyclic_relation[iff]:
  \<open>single_valued_range_acyclic_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
    single_valued_domain_acyclic_relation R\<close>  
  by (simp add: single_valued_domain_acyclic_relation_def
                single_valued_range_acyclic_relation_def)

lemma conv_single_valued_domain_acyclic_relation[iff]:
  \<open>single_valued_domain_acyclic_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
    single_valued_range_acyclic_relation R\<close>  
  by (simp add: single_valued_domain_acyclic_relation_def
                single_valued_range_acyclic_relation_def)

lemma conv_is_upper_bound_of[iff]:
  \<open>binary_relation.is_upper_bound_of (R\<inverse>\<inverse>) y x \<longleftrightarrow>
   binary_relation.is_lower_bound_of R y x\<close>
  by (auto simp: binary_relation.is_upper_bound_of_def
            binary_relation.is_lower_bound_of_def)

lemma conv_is_lower_bound_of[iff]:
  \<open>binary_relation.is_lower_bound_of (R\<inverse>\<inverse>) y x \<longleftrightarrow>
   binary_relation.is_upper_bound_of R y x\<close>
  by (auto simp: binary_relation.is_upper_bound_of_def
            binary_relation.is_lower_bound_of_def)

lemma tranclp_is_upper_bound_of[iff]:
  \<open>binary_relation.is_upper_bound_of (R\<^sup>+\<^sup>+) y x \<longleftrightarrow>
   binary_relation.is_upper_bound_of R y x\<close>
  apply (auto simp: binary_relation.is_upper_bound_of_def)  
  by (meson tranclpD)

lemma tranclp_is_lower_bound_of[iff]:
  \<open>binary_relation.is_lower_bound_of (R\<^sup>+\<^sup>+) y x \<longleftrightarrow>
   binary_relation.is_lower_bound_of R y x\<close>
  apply (auto simp: binary_relation.is_lower_bound_of_def)    
  by (metis tranclp.cases)

lemma conv_is_upper_order_of[iff]:
  \<open>binary_relation.is_upper_order_of (R\<inverse>\<inverse>) n x \<longleftrightarrow>
   binary_relation.is_lower_order_of R n x\<close>
  by (auto simp: binary_relation.is_upper_order_of_def
            binary_relation.is_lower_order_of_def)

lemma conv_is_lower_order_of[iff]:
  \<open>binary_relation.is_lower_order_of (R\<inverse>\<inverse>) n x \<longleftrightarrow>
   binary_relation.is_upper_order_of R n x\<close>
  by (auto simp: binary_relation.is_upper_order_of_def
            binary_relation.is_lower_order_of_def)

lemma conv_upper_bounded_relation_iff[iff]:
  \<open>upper_bounded_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   lower_bounded_relation R\<close>  
  by (simp add: lower_bounded_relation_def upper_bounded_relation_def)

lemma conv_lower_bounded_relation_iff[iff]:
  \<open>lower_bounded_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   upper_bounded_relation R\<close>  
  by (simp add: lower_bounded_relation_def upper_bounded_relation_def)

lemma tranclp_upper_bounded_relation_iff[iff]:
  \<open>upper_bounded_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow>
   upper_bounded_relation R\<close>  
  by (simp add: upper_bounded_relation_def)

lemma tranclp_lower_bounded_relation_iff[iff]:
  \<open>lower_bounded_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow>
   lower_bounded_relation R\<close>  
  by (simp add: lower_bounded_relation_def)

(* lemma conv_single_valued_range_acyclic_ub_relation[iff]:
  \<open>single_valued_range_acyclic_ub_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   single_valued_domain_acyclic_lb_relation R\<close>  
  by (simp add: single_valued_domain_acyclic_lb_relation_def 
                single_valued_range_acyclic_ub_relation_def)

lemma conv_single_valued_range_acyclic_lb_relation[iff]:
  \<open>single_valued_domain_acyclic_lb_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   single_valued_range_acyclic_ub_relation R\<close>  
  by (simp add: single_valued_domain_acyclic_lb_relation_def 
                single_valued_range_acyclic_ub_relation_def) *)

lemma conv_wellfounded_relation[iff]:
  \<open>wellfounded_relation (R\<inverse>\<inverse>) \<longleftrightarrow> noetherian_relation R\<close>
  by (auto simp: wellfounded_relation_def
                    noetherian_relation_def)

lemma conv_noetherian_relation[iff]:
  \<open>noetherian_relation (R\<inverse>\<inverse>) \<longleftrightarrow> wellfounded_relation R\<close>
  by (auto simp: wellfounded_relation_def
                    noetherian_relation_def)

lemma trancpl_wellfounded_relation[iff]:
  \<open>wellfounded_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow> wellfounded_relation R\<close>
  apply (auto simp: wellfounded_relation_def)
  subgoal by (metis tranclp.simps wfP_eq_minimal)  
  by (simp add: wfP_trancl)

lemma trancp_noetherian_relation[iff]:
  \<open>noetherian_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow> noetherian_relation R\<close>
proof 
  assume \<open>noetherian_relation (R\<^sup>+\<^sup>+)\<close>
  then have \<open>wellfounded_relation (R\<^sup>+\<^sup>+\<inverse>\<inverse>)\<close> by simp
  then have \<open>wellfounded_relation (R\<inverse>\<inverse>\<^sup>+\<^sup>+)\<close> by simp
  then have \<open>wellfounded_relation (R\<inverse>\<inverse>)\<close> 
    by (simp only: trancpl_wellfounded_relation)
  then show \<open>noetherian_relation R\<close> by simp
next
  assume \<open>noetherian_relation R\<close>
  then have \<open>wellfounded_relation (R\<inverse>\<inverse>)\<close> by simp
  then have \<open>wellfounded_relation (R\<inverse>\<inverse>\<^sup>+\<^sup>+)\<close> 
    by (simp only: trancpl_wellfounded_relation)
  then have \<open>wellfounded_relation (R\<^sup>+\<^sup>+\<inverse>\<inverse>)\<close> by simp
  then show \<open>noetherian_relation (R\<^sup>+\<^sup>+)\<close> by simp
qed

lemma conv_finite_lb_chains_relation[iff]:
  \<open>finite_lb_chains_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   finite_ub_chains_relation R\<close>  
  by (simp add: finite_lb_chains_relation_def finite_ub_chains_relation_def)

lemma conv_finite_ub_chains_relation[iff]:
  \<open>finite_ub_chains_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   finite_lb_chains_relation R\<close>  
  by (metis conv_finite_lb_chains_relation conversep_conversep)

lemma tranclp_finite_lb_chains_relation[iff]:
  \<open>finite_lb_chains_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow>
   finite_lb_chains_relation R\<close>  
  by (simp add: finite_lb_chains_relation_def)

lemma tranclp_finite_ub_chains_relation[iff]:
  \<open>finite_ub_chains_relation (R\<^sup>+\<^sup>+) \<longleftrightarrow>
   finite_ub_chains_relation R\<close>  
  by (metis conv_finite_lb_chains_relation conv_tranclp_eq tranclp_finite_lb_chains_relation)

lemma (in single_valued_range_relation)
  R_pow_unique_range_by_pow:
  assumes \<open>(R^^n) x y\<close> \<open>(R^^n) x z\<close>
  shows \<open>y = z\<close>
using assms proof (induct n arbitrary: x y z)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain y\<^sub>1 where Y1: \<open>(R^^n) x y\<^sub>1\<close> \<open>R y\<^sub>1 y\<close>
    using Suc(2) by auto
  obtain z\<^sub>1 where Z1: \<open>(R^^n) x z\<^sub>1\<close> \<open>R z\<^sub>1 z\<close>
    using Suc(3) by auto
  have \<open>y\<^sub>1 = z\<^sub>1\<close> using Suc(1) Y1(1) Z1(1) by blast
  then have \<open>R z\<^sub>1 y\<close> using Y1(2) by simp
  then show \<open>y = z\<close> using single_valued_range Z1(2) by simp
qed

lemma (in single_valued_range_relation)
  R_pow_diff_left[intro!]:
  assumes \<open>(R^^n\<^sub>y) x y\<close> \<open>(R^^n\<^sub>z) x z\<close> \<open>n\<^sub>y \<le> n\<^sub>z\<close>
  shows \<open>(R^^(n\<^sub>z-n\<^sub>y)) y z\<close>
proof (cases \<open>n\<^sub>y = n\<^sub>z\<close>)
  assume \<open>n\<^sub>y = n\<^sub>z\<close>
  then have \<open>(R^^n\<^sub>y) x z\<close> using \<open>(R^^n\<^sub>z) x z\<close> by simp
  then have \<open>y = z\<close> using \<open>(R^^n\<^sub>y) x y\<close> R_pow_unique_range_by_pow by simp
  then show ?thesis
    by (simp add: \<open>n\<^sub>y = n\<^sub>z\<close>)
next
  assume \<open>n\<^sub>y \<noteq> n\<^sub>z\<close>
  then have \<open>n\<^sub>y < n\<^sub>z\<close> using \<open>n\<^sub>y \<le> n\<^sub>z\<close> by auto
  then obtain \<delta> where \<delta>: \<open>n\<^sub>z = n\<^sub>y + \<delta>\<close>  \<open>0 < \<delta>\<close>
    using less_imp_add_positive by blast
  then have \<delta>_eq: \<open>\<delta> = n\<^sub>z - n\<^sub>y\<close> by simp
  then have \<open>(R^^(n\<^sub>y + \<delta>)) x z\<close> 
    using \<open>(R^^n\<^sub>z) x z\<close> \<delta>(1) by force
  then obtain q where \<open>(R^^n\<^sub>y) x q\<close> \<open>(R^^\<delta>) q z\<close>     
    by (metis relcomppE relpowp_add)
  then have \<open>q = y\<close> 
    using \<open>(R^^n\<^sub>y) x y\<close> R_pow_unique_range_by_pow
    by simp
  then show ?thesis using \<delta>_eq \<open>(R^^\<delta>) q z\<close> by simp
qed

lemma (in single_valued_domain_relation)
  R_pow_unique_domain_by_pow:
  assumes \<open>(R^^n) y x\<close> \<open>(R^^n) z x\<close>
  shows \<open>y = z\<close>
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.R_pow_unique_range_by_pow assms by simp
qed

lemma (in single_valued_domain_relation)
  R_pow_diff_right[intro!]:
  assumes \<open>(R^^n\<^sub>y) y x\<close> \<open>(R^^n\<^sub>z) z x\<close> \<open>n\<^sub>y \<le> n\<^sub>z\<close>
  shows \<open>(R^^(n\<^sub>z-n\<^sub>y)) z y\<close>
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.R_pow_diff_left assms by simp
qed

lemma (in single_valued_range_acyclic_relation)
  R_pow_unique:
  assumes \<open>(R^^n\<^sub>1) x y\<close> \<open>(R^^n\<^sub>2) x y\<close>
  shows \<open>n\<^sub>1 = n\<^sub>2\<close>
proof -
  have A: False if as: \<open>(R^^n\<^sub>1) x y\<close> \<open>(R^^n\<^sub>2) x y\<close> \<open>n\<^sub>1 < n\<^sub>2\<close> for n\<^sub>1 n\<^sub>2 x y
  proof -
    have AA: \<open>(R^^(n\<^sub>2 - n\<^sub>1)) y y\<close> 
      using as R_pow_diff_left by (meson less_or_eq_imp_le)
    have \<open>0 < (n\<^sub>2 - n\<^sub>1)\<close> using \<open>n\<^sub>1 < n\<^sub>2\<close> by auto
    then have \<open>R\<^sup>+\<^sup>+ y y\<close> using AA by (meson tranclp_power)
    then show False using acyclic by simp
  qed  
  show ?thesis
    apply (cases n\<^sub>1 n\<^sub>2 rule: linorder_cases ; simp)    
    using A assms by metis+
qed   

lemma (in single_valued_domain_acyclic_relation)
  R_pow_unique:
  assumes \<open>(R^^n\<^sub>1) x y\<close> \<open>(R^^n\<^sub>2) x y\<close>
  shows \<open>n\<^sub>1 = n\<^sub>2\<close>
proof -
  interpret P: single_valued_range_acyclic_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_acyclic_relation_axioms)
  show ?thesis
    using P.R_pow_unique assms by simp
qed

lemma (in single_valued_range_relation)
  unique_ub:
  assumes \<open>is_upper_bound_of y x\<close> \<open>is_upper_bound_of z x\<close>
  shows \<open>y = z\<close>
proof -
  obtain as1: \<open>R\<^sup>*\<^sup>* x y\<close> \<open>\<And>z. \<not> R y z\<close>
    using is_upper_bound_of_E assms(1) by metis
  obtain as2: \<open>R\<^sup>*\<^sup>* x z\<close> \<open>\<And>t. \<not> R z t\<close>
    using is_upper_bound_of_E assms(2) by metis
  obtain n\<^sub>y where \<open>(R^^n\<^sub>y) x y\<close> using as1(1)
    by (meson rtranclp_imp_relpowp)
  obtain n\<^sub>z where \<open>(R^^n\<^sub>z) x z\<close> using \<open>R\<^sup>*\<^sup>* x z\<close>
    by (meson rtranclp_imp_relpowp)
  have A: False if as: \<open>(R^^n\<^sub>y) x y\<close> \<open>(R^^n\<^sub>z) x z\<close> 
                      \<open>\<And>t. \<not> R y t\<close> \<open>n\<^sub>y < n\<^sub>z\<close> for n\<^sub>y n\<^sub>z z y x
  proof -
    have \<open>n\<^sub>y \<le> n\<^sub>z\<close> using \<open>n\<^sub>y < n\<^sub>z\<close> by simp
    then have \<open>(R^^(n\<^sub>z-n\<^sub>y)) y z\<close> 
      using \<open>(R^^n\<^sub>y) x y\<close> \<open>(R^^n\<^sub>z) x z\<close> by blast
    then have \<open>R\<^sup>+\<^sup>+ y z\<close> using \<open>n\<^sub>y < n\<^sub>z\<close> 
      by (meson tranclp_power zero_less_diff)
    then obtain q where \<open>R y q\<close> by (meson tranclpD)
    then show False using \<open>\<And>t. \<not> R y t\<close> by simp
  qed
  show ?thesis
    apply (cases n\<^sub>y n\<^sub>z rule: linorder_cases)
    subgoal using A \<open>(R^^n\<^sub>y) x y\<close> \<open>(R^^n\<^sub>z) x z\<close> as1 by metis
    subgoal using R_pow_unique_range_by_pow \<open>(R^^n\<^sub>y) x y\<close> \<open>(R^^n\<^sub>z) x z\<close> by metis
    using A \<open>(R^^n\<^sub>y) x y\<close> \<open>(R^^n\<^sub>z) x z\<close> as2 by metis
qed       

lemma (in single_valued_range_relation)
  is_upper_bound_ex1_I[intro!]:
  assumes \<open>\<exists>y. is_upper_bound_of y x\<close> 
  shows \<open>\<exists>!y. is_upper_bound_of y x\<close> 
  using assms unique_ub ex_ex1I 
  by meson

lemma (in single_valued_range_relation)
  upper_bound_eqI: 
  assumes \<open>is_upper_bound_of y x\<close> 
  shows \<open>upper_bound x = y\<close> 
  apply (simp add: upper_bound_def)
  using the1_equality[OF is_upper_bound_ex1_I] assms 
  by metis

lemma (in single_valued_range_relation)
  upper_bound_I: 
  assumes \<open>\<exists>y. is_upper_bound_of y x\<close> 
  shows \<open>is_upper_bound_of (upper_bound x) x\<close> 
  apply (simp add: upper_bound_def)
  using the1_equality[OF is_upper_bound_ex1_I] assms 
  by metis

lemma (in single_valued_range_acyclic_relation)
  unique_upper_order:
  assumes \<open>is_upper_order_of n x\<close> \<open>is_upper_order_of m x\<close>
  shows \<open>n = m\<close>
proof -
  obtain y where y: \<open>(R ^^ n) x y\<close> \<open>\<And>z. \<not> R y z\<close>
    using is_upper_order_of_E assms(1) by metis
  obtain z where z: \<open>(R ^^ m) x z\<close> \<open>\<And>t. \<not> R z t\<close>
    using is_upper_order_of_E assms(2) by metis
  have A: \<open>is_upper_bound_of y x\<close> using y    
    by (meson is_upper_bound_of_def rtranclp_power)
  have B: \<open>is_upper_bound_of z x\<close> using z
    by (meson is_upper_bound_of_def rtranclp_power)
  then have \<open>y = z\<close> using unique_ub A by simp
  then have \<open>(R ^^ m) x y\<close> using z by simp
  then show \<open>n = m\<close> using R_pow_unique y by simp
qed

lemma (in single_valued_range_acyclic_relation)
  is_upper_order_ex1_I[intro!]:
  assumes \<open>\<exists>n. is_upper_order_of n x\<close> 
  shows \<open>\<exists>!n. is_upper_order_of n x\<close> 
  using assms unique_upper_order ex_ex1I 
  by meson

lemma (in single_valued_range_acyclic_relation)
  upper_order_eqI: 
  assumes \<open>is_upper_order_of n x\<close> 
  shows \<open>upper_order x = n\<close> 
  apply (simp add: upper_order_def)
  using the1_equality[OF is_upper_order_ex1_I] assms 
  by metis

lemma (in single_valued_range_acyclic_relation)
  upper_order_I: 
  assumes \<open>\<exists>n. is_upper_order_of n x\<close> 
  shows \<open>is_upper_order_of (upper_order x) x\<close> 
  apply (simp add: upper_order_def)
  using the1_equality[OF is_upper_order_ex1_I] assms 
  by metis

lemma (in single_valued_domain_relation)
  unique_lb:
  assumes \<open>is_lower_bound_of y x\<close> \<open>is_lower_bound_of z x\<close>
  shows \<open>y = z\<close>
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.unique_ub[simplified] assms by simp
qed

lemma (in single_valued_domain_relation)
  is_lower_bound_ex1_I[intro!]:
  assumes \<open>is_lower_bound_of y x\<close> 
  shows \<open>\<exists>!y. is_lower_bound_of y x\<close> 
  using assms unique_lb ex_ex1I 
  by meson

lemma (in single_valued_domain_relation)
  lower_bound_eqI: 
  assumes \<open>is_lower_bound_of y x\<close> 
  shows \<open>lower_bound x = y\<close> 
  apply (simp add: lower_bound_def)
  using the1_equality[OF is_lower_bound_ex1_I] assms 
  by metis

lemma (in single_valued_domain_relation)
  lower_bound_I: 
  assumes \<open>\<exists>y. is_lower_bound_of y x\<close> 
  shows \<open>is_lower_bound_of (lower_bound x) x\<close> 
  apply (simp add: lower_bound_def)
  using the1_equality[OF is_lower_bound_ex1_I] assms 
  by metis

lemma (in single_valued_domain_acyclic_relation)
  unique_lower_order:
  assumes \<open>is_lower_order_of n x\<close> \<open>is_lower_order_of m x\<close>
  shows \<open>n = m\<close>
proof -
  interpret P: single_valued_range_acyclic_relation \<open>R\<inverse>\<inverse>\<close>     
    by (simp add: single_valued_domain_acyclic_relation_axioms)
  show ?thesis using P.unique_upper_order[simplified] assms by metis
qed

lemma (in single_valued_domain_acyclic_relation)
  is_lower_order_ex1_I[intro!]:
  assumes \<open>is_lower_order_of n x\<close> 
  shows \<open>\<exists>!n. is_lower_order_of n x\<close> 
  using assms unique_lower_order ex_ex1I 
  by meson

lemma (in single_valued_domain_acyclic_relation)
  lower_order_eqI: 
  assumes \<open>is_lower_order_of n x\<close> 
  shows \<open>lower_order x = n\<close> 
  apply (simp add: lower_order_def)
  using the1_equality[OF is_lower_order_ex1_I] assms 
  by metis

lemma (in single_valued_domain_acyclic_relation)
  lower_order_I: 
  assumes \<open>\<exists>n. is_lower_order_of n x\<close> 
  shows \<open>is_lower_order_of (lower_order x) x\<close>   
  using assms apply (elim exE)
  subgoal for n
    by (intro the1I2[OF is_lower_order_ex1_I,
        simplified lower_order_def[symmetric],
        of n x \<open>\<lambda>n. is_lower_order_of  n x\<close>] ; simp)
  done
    
lemma (in binary_relation) is_upper_bound_of_idemp:
  assumes \<open>is_upper_bound_of y x\<close> \<open>is_upper_bound_of z y\<close>
  shows \<open>z = y\<close>  
  using assms
  by (metis converse_rtranclpE is_upper_bound_of_E)

lemma (in binary_relation) is_lower_bound_of_idemp:
  assumes \<open>is_lower_bound_of y x\<close> \<open>is_lower_bound_of z y\<close>
  shows \<open>z = y\<close>  
  using assms  
  by (metis binary_relation.is_lower_bound_of_E rtranclpD tranclp.cases)

lemma (in single_valued_range_acyclic_relation)
  is_upper_order_of_ex_iff[simp]: 
  \<open>(\<exists>n. is_upper_order_of n x) \<longleftrightarrow> (\<exists>y. is_upper_bound_of y x)\<close>  
  by (metis binary_relation.is_upper_bound_of_def
            binary_relation.is_upper_order_of_I 
            is_upper_order_of_E rtranclp_power)

lemma (in single_valued_domain_acyclic_relation)
  is_lower_order_of_ex_iff[simp]: 
  \<open>(\<exists>n. is_lower_order_of n x) \<longleftrightarrow> (\<exists>y. is_lower_bound_of y x)\<close>  
  by (metis binary_relation.is_lower_bound_of_def
            binary_relation.is_lower_order_of_I 
            is_lower_order_of_E rtranclp_power)

lemma (in single_valued_range_relation) upper_bound_idemp[simp]:
  assumes \<open>\<exists>y. is_upper_bound_of y x\<close> 
  shows \<open>upper_bound (upper_bound x) = upper_bound x\<close>  
  apply (rule upper_bound_eqI[of \<open>upper_bound x\<close> \<open>upper_bound x\<close>])
  using upper_bound_I[OF assms] 
  by blast

lemma (in single_valued_range_acyclic_relation) is_upper_order_of_diff:
  assumes \<open>is_upper_order_of n\<^sub>x x\<close> \<open>is_upper_order_of n\<^sub>y y\<close> \<open>(R^^n) x y\<close>
  shows \<open>n = n\<^sub>x - n\<^sub>y\<close>
proof -
  obtain x\<^sub>1 where A1: \<open>(R^^n\<^sub>x) x x\<^sub>1\<close> \<open>\<And>z. \<not> R x\<^sub>1 z\<close> 
    using assms(1) is_upper_order_of_E by metis
  obtain y\<^sub>1 where A2: \<open>(R^^n\<^sub>y) y y\<^sub>1\<close> \<open>\<And>z. \<not> R y\<^sub>1 z\<close> 
    using assms(2) is_upper_order_of_E by metis
  have B: \<open>is_upper_bound_of x\<^sub>1 x\<close> using A1 
    by (meson is_upper_bound_of_def rtranclp_power)
  have C: \<open>(R^^(n + n\<^sub>y)) x y\<^sub>1\<close>
    apply (simp add: relpowp_add)
    using assms(3) A2(1) by blast
  then have \<open>is_upper_order_of (n + n\<^sub>y) x\<close>
    using A2(2) by blast
  then have \<open>n\<^sub>x = n + n\<^sub>y\<close> using assms(1) unique_upper_order by metis
  then show ?thesis 
    by presburger
qed

lemma (in single_valued_domain_acyclic_relation) is_lower_order_of_diff:
  assumes \<open>is_lower_order_of n\<^sub>x x\<close> \<open>is_lower_order_of n\<^sub>y y\<close> \<open>(R^^n) y x\<close>
  shows \<open>n = n\<^sub>x - n\<^sub>y\<close>
proof -
  interpret P: single_valued_range_acyclic_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_acyclic_relation_axioms)
  show ?thesis
    using assms P.is_upper_order_of_diff[simplified] by metis
qed

lemma (in single_valued_range_acyclic_relation) upper_order_diff:
  assumes \<open>\<exists>n\<^sub>x. is_upper_order_of n\<^sub>x x\<close> 
          \<open>\<exists>n\<^sub>y. is_upper_order_of n\<^sub>y y\<close> 
          \<open>R\<^sup>*\<^sup>* x y\<close>
  shows \<open>(R^^(upper_order x - upper_order y)) x y\<close>
proof -
  have A: \<open>is_upper_order_of (upper_order x) x\<close> 
    using assms(1) upper_order_I 
    by presburger
  have B: \<open>is_upper_order_of (upper_order y) y\<close> 
    using assms(2) upper_order_I 
    by presburger
  obtain n where C: \<open>(R^^n) x y\<close>
    using assms(3) by (meson rtranclp_power)
  show ?thesis
    using C is_upper_order_of_diff[OF A B C] by simp
qed

lemma (in single_valued_domain_acyclic_relation) lower_order_diff:
  assumes \<open>\<exists>n\<^sub>x. is_lower_order_of n\<^sub>x x\<close> 
          \<open>\<exists>n\<^sub>y. is_lower_order_of n\<^sub>y y\<close> 
          \<open>R\<^sup>*\<^sup>* y x\<close>
  shows \<open>(R^^(lower_order x - lower_order y)) y x\<close>
proof -
  interpret P: single_valued_range_acyclic_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_acyclic_relation_axioms)
  have A[simp]: \<open>P.upper_order x = lower_order x\<close>    
    using P.upper_order_eqI assms(1) lower_order_eqI by force
  have B[simp]: \<open>P.upper_order y = lower_order y\<close>    
    using P.upper_order_eqI assms(2) lower_order_eqI by force
  show ?thesis
    using P.upper_order_diff[simplified,OF assms[simplified]]
    by auto
qed

lemma (in single_valued_range_acyclic_relation)
  is_upper_order_of_ex1_iff[iff]:
  \<open>(\<exists>!n. is_upper_order_of n x) \<longleftrightarrow> (\<exists>y. is_upper_bound_of y x)\<close>
proof 
  assume assms: \<open>\<exists>y. is_upper_bound_of y x\<close>
  show \<open>\<exists>!n. is_upper_order_of n x\<close>
    apply (intro ex_ex1I)
    subgoal by (simp add: assms)  
    by (simp add: unique_upper_order)
next
  assume assms: \<open>\<exists>!n. is_upper_order_of n x\<close>
  then show \<open>\<exists>y. is_upper_bound_of y x\<close>        
    using is_upper_order_of_ex_iff by blast    
qed

lemma (in single_valued_range_relation)
  is_upper_bound_of_ex1_iff[simp]:
  \<open>(\<exists>!y. is_upper_bound_of y x) \<longleftrightarrow> (\<exists>y. is_upper_bound_of y x)\<close>
  by auto


lemma (in single_valued_domain_acyclic_relation)
  is_lower_order_of_ex1_iff[iff]:
  \<open>(\<exists>!n. is_lower_order_of n x) \<longleftrightarrow> (\<exists>y. is_lower_bound_of y x)\<close>
proof 
  assume assms: \<open>\<exists>y. is_lower_bound_of y x\<close>
  show \<open>\<exists>!n. is_lower_order_of n x\<close>
    apply (intro ex_ex1I)
    subgoal
      by (meson assms is_lower_bound_of_def is_lower_order_of_I 
                rtranclp_power) 
    by (simp add: unique_lower_order)
next
  assume assms: \<open>\<exists>!n. is_lower_order_of n x\<close>
  then show \<open>\<exists>y. is_lower_bound_of y x\<close>        
    using is_lower_order_of_ex_iff by blast    
qed

lemma (in single_valued_domain_relation)
  is_lower_bound_of_ex1_iff[simp]:
  \<open>(\<exists>!y. is_lower_bound_of y x) \<longleftrightarrow> (\<exists>y. is_lower_bound_of y x)\<close>  
  by (meson unique_lb)  


lemma (in single_valued_range_relation)
  cycle_pump:
  assumes \<open>(R^^n) x x\<close> 
  shows \<open>(R^^(m*n)) x x\<close> 
proof (induct m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have A: \<open>n + m * n = m * n + n\<close> by presburger
  have B: \<open>(R ^^ (m * n + n)) x x \<longleftrightarrow> (\<exists>y. (R ^^ (m * n)) x y \<and> (R ^^ n) y x)\<close>      
      by (metis Suc.hyps assms(1) relcomppI relpowp_add)    
  show ?case
    apply (simp add: A B ; intro exI[of _ x])
    using Suc assms(1) by auto    
qed

lemma (in single_valued_domain_relation)
  cycle_pump:
  assumes \<open>(R^^n) x x\<close> 
  shows \<open>(R^^(m*n)) x x\<close>
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.cycle_pump[simplified] assms by metis
qed

lemma (in single_valued_range_relation)
  cycle_ex_any_pow_left:
  assumes \<open>R\<^sup>+\<^sup>+ x x\<close> 
  shows \<open>\<exists>!y. (R^^n) x y\<close> 
proof -
  obtain m where \<open>(R^^m) x x\<close> \<open>0 < m\<close>
    using assms by (meson tranclp_power)
  have n: \<open>n = (n div m)*m + (n mod m)\<close> by presburger
  have A: \<open>(R^^((n div m)*m)) x x\<close> using cycle_pump \<open>(R^^m) x x\<close> by metis
  
  have \<open>n mod m < m\<close> using \<open>0 < m\<close> by simp
  then obtain y where B: \<open>(R^^(n mod m)) x y\<close> using \<open>(R^^m) x x\<close>    
    by (metis less_imp_add_positive relcomppE relpowp_add)
  have \<open>(R^^((n div m)*m + (n mod m))) x y\<close>
    using A B by (metis relcomppI relpowp_add)
  then have R1: \<open>(R^^n) x y\<close> using n by auto
  then have R2: \<open>z = y\<close> if \<open>(R^^n) x z\<close> for z
    using R_pow_unique_range_by_pow that by metis 
  show ?thesis
    apply (intro ex1I[of _ y] R1)
    using R2 by metis
qed

lemma (in single_valued_domain_relation)
  cycle_ex_any_pow_right:
  assumes \<open>R\<^sup>+\<^sup>+ x x\<close> 
  shows \<open>\<exists>!y. (R^^n) y x\<close> 
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.cycle_ex_any_pow_left[of x,simplified] assms by metis  
qed

lemma (in single_valued_range_relation)
  cycle_symmetry_left:
  assumes \<open>R\<^sup>+\<^sup>+ x x\<close> \<open>(R^^n) x y\<close>
  shows \<open>R\<^sup>*\<^sup>* y x\<close>
using assms(2) proof (induct n arbitrary: y)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain z where \<open>(R ^^ n) x z\<close> \<open>R z y\<close> by auto
  obtain m where \<open>(R^^m) x x\<close> \<open>0 < m\<close> 
    using assms(1) by (meson tranclp_power)
  obtain k where \<open>n < k*m\<close> using \<open>0 < m\<close>    
    by (metis dividend_less_times_div mult.commute mult_Suc_right)
  have \<open>(R^^(k*m)) x x\<close> using \<open>(R^^m) x x\<close> cycle_pump by metis
  then obtain t where \<open>(R^^n) x t\<close> \<open>R\<^sup>*\<^sup>* t x\<close> 
    using \<open>n < k*m\<close> Suc.hyps \<open>(R ^^ n) x z\<close> by blast
  then have \<open>t = z\<close> using \<open>(R ^^ n) x z\<close> R_pow_unique_range_by_pow by simp
  then have \<open>R\<^sup>*\<^sup>* z x\<close> using \<open>R\<^sup>*\<^sup>* t x\<close> by simp  
  have \<open>R\<^sup>+\<^sup>+ z x\<close>  
  proof (cases \<open>z = x\<close>)
    assume \<open>z = x\<close>
    then show ?thesis using \<open>R\<^sup>+\<^sup>+ x x\<close> by metis
  next
    assume \<open>z \<noteq> x\<close>
    then show ?thesis 
      using \<open>R\<^sup>*\<^sup>* z x\<close> assms(1) by auto
  qed
  then obtain u where \<open>R z u\<close> \<open>R\<^sup>*\<^sup>* u x\<close> 
    by (metis tranclpD) 
  then have \<open>u = y\<close> using \<open>R z y\<close> single_valued_range by simp
  then show \<open>R\<^sup>*\<^sup>* y x\<close> using \<open>R\<^sup>*\<^sup>* u x\<close> by simp
qed

lemma (in single_valued_domain_relation)
  cycle_symmetry_right:
  assumes \<open>R\<^sup>+\<^sup>+ x x\<close> \<open>(R^^n) y x\<close>
  shows \<open>R\<^sup>*\<^sup>* x y\<close>
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.cycle_symmetry_left[of x,simplified] assms by metis  
qed

lemma (in single_valued_range_relation)
  cycles_exclude_upper_bounds:
  assumes \<open>R\<^sup>+\<^sup>+ x x\<close> \<open>R\<^sup>*\<^sup>* x y\<close> \<open>\<And>z. \<not> R y z\<close>
  shows False
  using cycle_symmetry_left[OF assms(1)] assms 
  by (metis rtranclpD rtranclp_power tranclpD)

lemma (in single_valued_domain_relation)
  cycles_exclude_lower_bounds:
  assumes \<open>R\<^sup>+\<^sup>+ x x\<close> \<open>R\<^sup>*\<^sup>* y x\<close> \<open>\<And>z. \<not> R z y\<close>
  shows False
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.cycles_exclude_upper_bounds[of x,simplified] assms by metis  
qed

lemma (in single_valued_range_relation)
  same_domain_exhausts[consumes 2,cases pred]:
  assumes \<open>R\<^sup>*\<^sup>* x y\<close> \<open>R\<^sup>*\<^sup>* x z\<close> 
  obtains (yz) \<open>R\<^sup>*\<^sup>* y z\<close> | (zy) \<open>R\<^sup>*\<^sup>* z y\<close>   
proof -
  have \<open>R\<^sup>*\<^sup>* y z \<or> R\<^sup>*\<^sup>* z y\<close>
  using assms
  proof(induct x y arbitrary: z)
    case (rtrancl_refl a z)
    then show ?case by simp
  next
    case (rtrancl_into_rtrancl a b c z)
    then show ?case using single_valued_range 
      by (metis converse_rtranclpE rtranclp.rtrancl_into_rtrancl)
  qed
  then show ?thesis
    using that by metis
qed

lemma (in single_valued_domain_relation)
  same_range_exhausts[consumes 2,cases pred]:
  assumes \<open>R\<^sup>*\<^sup>* y x\<close> \<open>R\<^sup>*\<^sup>* z x\<close> 
  obtains (yz) \<open>R\<^sup>*\<^sup>* y z\<close> | (zy) \<open>R\<^sup>*\<^sup>* z y\<close>
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  show ?thesis
    using P.same_domain_exhausts[simplified,OF assms] that
    by metis
qed
   
sublocale single_valued_range_upper_bounded_relation
          \<subseteq> acyclic_relation
proof (unfold_locales ; intro notI)
  fix x
  assume \<open>R\<^sup>+\<^sup>+ x x\<close>
  obtain y where \<open>is_upper_bound_of y x\<close>
    using upper_bounded by blast
  then obtain \<open>R\<^sup>*\<^sup>* x y\<close> \<open>\<And>z. \<not> R y z\<close>
    using is_upper_bound_of_E by blast
  then show False 
    using cycles_exclude_upper_bounds \<open>R\<^sup>+\<^sup>+ x x\<close>
    by metis
qed

sublocale single_valued_domain_lower_bounded_relation
          \<subseteq> acyclic_relation
proof -
  interpret P: single_valued_range_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_relation_axioms)
  have \<open>acyclic_relation (R\<inverse>\<inverse>)\<close> 
    by (meson acyclic_relation_def conv_acyclic_relation 
              cycles_exclude_lower_bounds is_lower_bound_of_E lower_bounded)
  then show \<open>acyclic_relation R\<close> by simp
qed

lemma conv_single_valued_range_upper_bounded_relation[iff]:
  \<open>single_valued_range_upper_bounded_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   single_valued_domain_lower_bounded_relation R\<close>  
  by (simp add: single_valued_domain_lower_bounded_relation_def
                single_valued_range_upper_bounded_relation_def)

lemma conv_single_valued_domain_lower_bounded_relation[iff]:
  \<open>single_valued_domain_lower_bounded_relation (R\<inverse>\<inverse>) \<longleftrightarrow>
   single_valued_range_upper_bounded_relation R\<close>  
  by (simp add: single_valued_domain_lower_bounded_relation_def
                single_valued_range_upper_bounded_relation_def)

lemma (in single_valued_range_upper_bounded_relation)
    all_unique_upper_bound: 
  \<open>\<exists>!y. is_upper_bound_of y x\<close> 
  by simp

lemma (in single_valued_range_upper_bounded_relation)
    all_unique_upper_order: 
  \<open>\<exists>!n. is_upper_order_of n x\<close>   
proof -
  interpret single_valued_range_acyclic_relation R    
    by (simp add: acyclic_relation_axioms 
                  single_valued_range_acyclic_relation_def 
                  single_valued_range_relation_axioms)
  show ?thesis by simp
qed

lemma (in single_valued_domain_lower_bounded_relation)
    all_unique_lower_bound: 
  \<open>\<exists>!y. is_lower_bound_of y x\<close> 
  by simp

lemma (in single_valued_domain_lower_bounded_relation)
    all_unique_lower_order: 
  \<open>\<exists>!n. is_lower_order_of n x\<close>   
proof -
  interpret P: single_valued_range_upper_bounded_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_domain_lower_bounded_relation_axioms)
  
  show ?thesis
    using P.all_unique_upper_order[simplified] by metis
qed

(* 
locale single_valued_range_upper_bounded_relation =
  single_valued_range_relation + upper_bounded_relation

locale single_valued_domain_lower_bounded_relation =
  single_valued_domain_relation + lower_bounded_relation

locale wellfounded_relation =
  binary_relation +
    assumes
      wellfounded: \<open>wfP R\<close>

locale noetherian_relation =
  binary_relation +
    assumes
      noetherian: \<open>wfP R\<inverse>\<inverse>\<close>

*)

sublocale single_valued_domain_lower_bounded_relation
  \<subseteq> single_valued_domain_wellfounded_relation
proof (unfold_locales)
  interpret single_valued_domain_acyclic_relation R
    by intro_locales
  have A: \<open>\<exists>z\<in>X. \<forall>y. R y z \<longrightarrow> y \<notin> X\<close> if \<open>x \<in> X\<close> for x X
  proof -    
    define Y where \<open>Y \<equiv> { y . y \<in> X \<and> R\<^sup>*\<^sup>* y x }\<close>
    have \<open>is_lower_order_of (lower_order x) x\<close>
      using lower_order_I by simp
    then have \<open>(R^^(lower_order x)) (lower_bound x) x\<close>
      by (metis is_lower_bound_of_I is_lower_order_of_E lower_bound_eqI relpowp_imp_rtranclp)
    have n_lo: \<open>n \<le> lower_order x\<close> if\<open>(R^^n) y x\<close> for y n      
      by (metis R_pow_unique all_unique_lower_order diff_le_self lower_order_diff
                relpowp_imp_rtranclp that)
    define Z where \<open>Z \<equiv> { n | n y . y \<in> Y \<and> (R^^n) y x }\<close>
    have Z_I: \<open>n \<in> Z\<close> if \<open>y \<in> Y\<close> \<open>(R^^n) y x\<close> for y n
      using that by (auto simp: Z_def)
    have \<open>Z \<noteq> \<emptyset>\<close> 
      apply (simp add: Z_def Y_def)      
      by (meson \<open>x \<in> X\<close> relpowp_0_I rtranclp.rtrancl_refl)
        
    have Z_lo: \<open>n \<le> lower_order x\<close> if \<open>n \<in> Z\<close> for n
      using that apply (simp add: Z_def)
      using n_lo by blast
    then have finZ: \<open>finite Z\<close> 
      using finite_nat_set_iff_bounded_le by auto
    then have \<open>Max Z \<in> Z\<close>
      by (intro Max_in \<open>Z \<noteq> \<emptyset>\<close> ; simp)
    have max_z_max: \<open>z \<le> Max Z\<close> if \<open>z \<in> Z\<close> for z
      using \<open>Z \<noteq> \<emptyset>\<close> finZ 
      by (simp add: that)
    obtain z where \<open>z \<in> Y\<close> \<open>(R^^(Max Z)) z x\<close> 
      using \<open>Max Z \<in> Z\<close> Z_def by blast
    have \<open>z \<in> X\<close> using \<open>z \<in> Y\<close> Y_def by auto
    have q_min: \<open>q \<notin> X\<close> if \<open>R q z\<close> for q      
    proof 
      have AA: \<open>(R^^(Suc(Max Z))) q x\<close>
        using \<open>(R^^(Max Z)) z x\<close> that by (meson relpowp_Suc_I2)
      assume \<open>q \<in> X\<close>
      then have \<open>q \<in> Y\<close>
        apply (auto simp: Y_def)        
        by (meson AA rtranclp_power \<open>R q z\<close> \<open>(R^^(Max Z)) z x\<close>)
      have \<open>Suc (Max Z) \<in> Z\<close>
        by (intro Z_I[of q] \<open>q \<in> Y\<close> AA)
      then show False 
        using max_z_max[of \<open>Suc (Max Z)\<close>] by simp
    qed
    show ?thesis
      by (intro bexI[of _ z] \<open>z \<in> X\<close> allI impI q_min ; simp)
  qed
  show \<open>wfP R\<close>
    apply (simp add: wfP_eq_minimal ; auto)
    using A by metis
qed

sublocale single_valued_range_upper_bounded_relation
        \<subseteq> single_valued_range_noetherian_relation  
proof (unfold_locales)
  interpret P: single_valued_domain_lower_bounded_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: single_valued_range_upper_bounded_relation_axioms)
  show \<open>wfP R\<inverse>\<inverse>\<close> using P.wellfounded by simp
qed

lemma (in single_valued_domain_wellfounded_relation)
  is_lower_bounded_relation[simp,intro]:
  \<open>single_valued_domain_lower_bounded_relation R\<close>
proof (unfold_locales)
  fix x
  define X where \<open>X \<equiv> { y . R\<^sup>*\<^sup>* y x }\<close>
  have \<open>x \<in> X\<close> by (auto simp: X_def)
  then obtain z where z: \<open>z \<in> X\<close> \<open>\<And>y. R y z \<Longrightarrow> y \<notin> X\<close>
    using wellfounded[simplified wfP_eq_minimal] by metis
  have R1: \<open>R\<^sup>*\<^sup>* z x\<close> using \<open>z \<in> X\<close> by (auto simp: X_def)
  have R2: \<open>\<not> R y z\<close> for y    
  proof
    assume \<open>R y z\<close>
    then have \<open>R\<^sup>*\<^sup>* y x\<close> using \<open>z \<in> X\<close> X_def by auto
    then have \<open>y \<in> X\<close> by (auto simp: X_def)
    then show False using \<open>R y z\<close> z(2) by simp
  qed 
  then have \<open>is_lower_bound_of z x\<close>    
    by (intro is_lower_bound_of_I R1 ; simp?)
  then show \<open>\<exists>y. is_lower_bound_of y x\<close> by blast
qed

lemma (in single_valued_range_noetherian_relation)
  is_upper_bounded_relation[simp,intro]:
  \<open>single_valued_range_upper_bounded_relation R\<close>
proof -
  interpret P: single_valued_domain_wellfounded_relation \<open>R\<inverse>\<inverse>\<close>    
    by (simp add: noetherian_relation_axioms single_valued_domain_wellfounded_relation_def
                  single_valued_range_relation_axioms)
  show ?thesis
    using P.is_lower_bounded_relation by simp
qed

lemma single_valued_domain_lb_eq_wf:
      \<open>single_valued_domain_lower_bounded_relation =
       single_valued_domain_wellfounded_relation\<close>
proof (intro ext iffI)
  fix R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assume A: \<open>single_valued_domain_lower_bounded_relation R\<close>
  then interpret single_valued_domain_lower_bounded_relation R .
  show \<open>single_valued_domain_wellfounded_relation R\<close>    
    by (simp add: single_valued_domain_wellfounded_relation_axioms)
next
  fix R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assume A: \<open>single_valued_domain_wellfounded_relation R\<close>
  then interpret single_valued_domain_wellfounded_relation R .
  show \<open>single_valued_domain_lower_bounded_relation R\<close> by auto
qed

lemma single_valued_range_ub_eq_noetherian:
  \<open>single_valued_range_upper_bounded_relation =
   single_valued_range_noetherian_relation\<close>
proof  (intro ext iffI)
  fix R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assume A: \<open>single_valued_range_upper_bounded_relation R\<close>
  then interpret single_valued_range_upper_bounded_relation R .
  show \<open>single_valued_range_noetherian_relation R\<close>    
    by (simp add: single_valued_range_noetherian_relation_axioms)
next
  fix R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assume A: \<open>single_valued_range_noetherian_relation R\<close>
  then interpret single_valued_range_noetherian_relation R .
  show \<open>single_valued_range_upper_bounded_relation R\<close> by auto
qed

lemma single_valued_range_acyclic_finite_lb_chains_relation_ub:
  \<open>single_valued_range_acyclic_finite_lb_chains_relation R \<longleftrightarrow>
   single_valued_range_upper_bounded_relation R\<close>
proof 
  assume \<open>single_valued_range_acyclic_finite_lb_chains_relation R\<close>
  then interpret single_valued_range_acyclic_finite_lb_chains_relation R .
  show \<open>single_valued_range_upper_bounded_relation R\<close>
  proof (unfold_locales)
    fix x
    define X where \<open>X \<equiv> { y . R\<^sup>*\<^sup>* x y }\<close>
    have \<open>x \<in> X\<close> by (auto simp: X_def)
    then have A: \<open>X \<noteq> \<emptyset>\<close> by blast
    have B: \<open>R\<^sup>*\<^sup>* y z \<or> R\<^sup>*\<^sup>* z y\<close> if \<open>y \<in> X\<close> \<open>z \<in> X\<close> for y z
      using that apply (auto simp: X_def)      
      by (meson same_domain_exhausts)      
    have C: \<open>\<exists>x \<in> X. \<forall>y \<in> X. R\<^sup>*\<^sup>* x y\<close>
      by (intro bexI[of _ x] \<open>x \<in> X\<close> ; auto simp: X_def)
    have D: \<open>lb_chain R X\<close>
      using A B C by (unfold_locales ; metis)
    then have \<open>finite X\<close> using finite_lb_chains by simp
    define Y where \<open>Y \<equiv> { n | n y . y \<in> X \<and> (R^^n) x y}\<close>
    have \<open>Y \<noteq> \<emptyset>\<close> 
      apply (auto simp: Y_def)
      by (intro exI[of _ x] exI[of _ 0] ; simp add: \<open>x \<in> X\<close>)
    have \<open>\<exists>!y. (R^^n) x y\<close> if \<open>n \<in> Y\<close> for n 
      using that R_pow_unique_range_by_pow 
      by (auto simp: Y_def)
    then obtain f where f: \<open>(R^^n) x (f n)\<close> if \<open>n \<in> Y\<close> for n
      using that by moura
    have f_inj: \<open>inj_on f Y\<close>
      using f apply (auto intro!: inj_onI)      
      by (metis R_pow_unique)
    have f_img: \<open>f ` Y = X\<close>
      using f apply (auto simp: Y_def X_def image_iff)
      subgoal by (meson rtranclp_power)      
      by (meson R_pow_unique_range_by_pow rtranclp_power)
    then have f_bij: \<open>bij_betw f Y X\<close> 
      using f_inj by (meson bij_betw_imageI)
    then have fin_Y: \<open>finite Y\<close> 
      using \<open>finite X\<close> bij_betw_finite by blast
    then obtain max_y: \<open>Max Y \<in> Y\<close> \<open>\<And>n. n \<in> Y \<Longrightarrow> n \<le> Max Y\<close>
      using \<open>Y \<noteq> \<emptyset>\<close> by simp
    then have \<open>f (Max Y) \<in> X\<close> using f_img by blast    
    have no_upper: \<open>\<not> R\<^sup>+\<^sup>+ (f (Max Y)) y\<close> if \<open>y \<in> X\<close> for y
    proof
      assume as: \<open>R\<^sup>+\<^sup>+ (f (Max Y)) y\<close>
      then obtain k where \<open>R (f (Max Y)) k\<close> 
        by (metis converse_tranclpE)
      then have AA: \<open>(R^^(Suc (Max Y))) x k\<close> 
        using f \<open>Max Y \<in> Y\<close> by (meson relpowp_Suc_I)
      then have \<open>R\<^sup>*\<^sup>* x k\<close> by (meson rtranclp_power)
      then have \<open>k \<in> X\<close> by (auto simp: X_def)
      then have \<open>Suc (Max Y) \<in> Y\<close> using AA by (auto simp: Y_def)
      then have \<open>Suc (Max Y) \<le> Max Y\<close> using max_y by simp
      then show False by simp
    qed
    then have R1: \<open>R\<^sup>*\<^sup>* y (f (Max Y))\<close> if \<open>y \<in> X\<close> for y
      by (metis B Nitpick.rtranclp_unfold \<open>f (Max Y) \<in> X\<close> that) 
    have R2: \<open>\<not> R (f (Max Y)) y\<close> for y
    proof
      assume as: \<open>R (f (Max Y)) y\<close>
      then have \<open>R\<^sup>*\<^sup>* x y\<close> 
        by (meson R1 \<open>x \<in> X\<close> rtranclp.rtrancl_into_rtrancl)
      then have \<open>y \<in> X\<close> by (auto simp: X_def)
      then have \<open>\<not> R\<^sup>+\<^sup>+ (f (Max Y)) y\<close> using no_upper by simp
      then show False using as by auto
    qed
    show \<open>\<exists>y. is_upper_bound_of y x\<close>
      by (intro exI[of _ \<open>f (Max Y)\<close>] is_upper_bound_of_I R1 R2 \<open>x \<in> X\<close>)
  qed
next
  assume \<open>single_valued_range_upper_bounded_relation R\<close>
  then interpret single_valued_range_upper_bounded_relation R .
  show \<open>single_valued_range_acyclic_finite_lb_chains_relation R\<close>
  proof (unfold_locales)
    fix A
    assume as: \<open>lb_chain R A\<close>
    then obtain x where x: \<open>chain R A\<close> \<open>x \<in> A\<close> \<open>\<And>y. y \<in> A \<Longrightarrow> R\<^sup>*\<^sup>* x y\<close>      
      by (meson lb_chain.lb_exists lb_chain_def)
    define X where \<open>X \<equiv> { y . R\<^sup>*\<^sup>* x y }\<close>
    have \<open>A \<subseteq> X\<close> by (auto simp: X_def x)
    obtain z where z: \<open>R\<^sup>*\<^sup>* x z\<close> \<open>\<And>y. \<not> R z y\<close> 
      using upper_bounded 
      by (meson is_upper_bound_of_E)
    then obtain \<open>x \<in> X\<close> \<open>z \<in> X\<close> by (auto simp: X_def)
    define Y where \<open>Y \<equiv> { n | n y . y \<in> X \<and> (R^^n) x y}\<close>
    have \<open>Y \<noteq> \<emptyset>\<close> 
      apply (auto simp: Y_def)
      by (intro exI[of _ x] exI[of _ 0] ; simp add: \<open>x \<in> X\<close>)
    have \<open>\<exists>!y. (R^^n) x y\<close> if \<open>n \<in> Y\<close> for n 
      using that R_pow_unique_range_by_pow 
      by (auto simp: Y_def)
    then obtain f where f: \<open>(R^^n) x (f n)\<close> if \<open>n \<in> Y\<close> for n
      using that by moura
    have f_inj: \<open>inj_on f Y\<close>
      using f apply (auto intro!: inj_onI)      
      by (metis acyclic_relation_axioms single_valued_range_acyclic_relation.R_pow_unique
                single_valued_range_acyclic_relation_def single_valued_range_relation_axioms)      
    have f_img: \<open>f ` Y = X\<close>
      using f apply (auto simp: Y_def X_def image_iff)
      subgoal by (meson rtranclp_power)      
      by (meson R_pow_unique_range_by_pow rtranclp_power)
    then have f_bij: \<open>bij_betw f Y X\<close> 
      using f_inj by (meson bij_betw_imageI)
    obtain n\<^sub>z where nz: \<open>n\<^sub>z \<in> Y\<close> \<open>f n\<^sub>z = z\<close> 
      using \<open>z \<in> X\<close> f_img by blast
    then have \<open>(R^^n\<^sub>z) x z\<close> using f by blast
    have \<open>n \<le> n\<^sub>z\<close> if \<open>n \<in> Y\<close> for n
    proof (rule ccontr)
      assume \<open>\<not> n \<le> n\<^sub>z\<close>
      then obtain \<delta> where \<delta>: \<open>n = n\<^sub>z + \<delta>\<close> \<open>0 < \<delta>\<close> 
        by (metis less_imp_add_positive not_less)
      obtain q where \<open>q \<in> X\<close> \<open>(R^^n) x q\<close> using \<open>n \<in> Y\<close> Y_def by auto
      then have \<open>(R^^(n\<^sub>z + \<delta>)) x q\<close> using \<delta> by simp
      then obtain k where \<open>(R^^n\<^sub>z) x k\<close> \<open>(R^^\<delta>) k q\<close> 
        by (metis relcomppE relpowp_add)
      then have \<open>k = z\<close> using \<open>(R^^n\<^sub>z) x z\<close> R_pow_unique_range_by_pow by simp
      then have \<open>(R^^\<delta>) z q\<close> using \<open>(R^^\<delta>) k q\<close> by simp
      then have \<open>R\<^sup>+\<^sup>+ z q\<close> using \<delta> by (meson tranclp_power)
      then obtain z\<^sub>1 where \<open>R z z\<^sub>1\<close> by (meson tranclpD)
      then show False using z by simp
    qed    
    then have fin_Y: \<open>finite Y\<close>       
      using finite_nat_set_iff_bounded_le by auto
    then show \<open>finite A\<close>
      using f_bij bij_betw_finite \<open>A \<subseteq> X\<close> finite_subset 
      by metis
  qed
qed

no_notation emptySet (\<open>\<emptyset>\<close>)

end