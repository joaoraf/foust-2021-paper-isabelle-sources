theory Inherence
  imports PossibleWorlds Chains
begin 

text_raw \<open>\Copy{locale:inherence-sig}{\<close>
locale inherence_sig = 
    possible_worlds_alt_sig where \<W> = \<W>
  for \<W> :: \<open>'e set set\<close> +
  fixes
    inheresIn :: \<open>'e \<Rightarrow> 'e \<Rightarrow> bool\<close> (infix \<open>\<triangleleft>\<close> 75)
text_raw \<open>}\<close>

sublocale inherence_sig \<subseteq> inh: binary_relation \<open>(\<triangleleft>)\<close> .

record 'e inherence_model = 
  im_\<W> :: \<open>'e set set\<close>
  im_inheresIn :: \<open>'e \<Rightarrow> 'e \<Rightarrow> bool\<close>

text_raw \<open>\Copy{locale:inherence-base}{\<close>
locale inherence_base =
  inherence_sig +
  possible_worlds_alt +
  assumes
    inherence_imp_ed: \<open>x \<triangleleft> y \<Longrightarrow> ed x y\<close> and    
    moment_non_migration: \<open>\<lbrakk> x \<triangleleft> y ; x \<triangleleft> z \<rbrakk> \<Longrightarrow> y = z\<close> 
text_raw \<open>}\<close>

text_raw \<open>\Copy{locale:inherence-original}{\<close>
locale inherence_original =
  inherence_base +
  assumes
    inherence_scope: \<open>x \<triangleleft> y \<Longrightarrow> x \<in> \<E> \<and> y \<in> \<E>\<close> and
    inherence_irrefl: \<open>\<not> x \<triangleleft> x\<close> and
    inherence_asymm: \<open>x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close> and
    inherence_antitrgansitive: "\<lbrakk> x \<triangleleft> y ; y \<triangleleft> z \<rbrakk> \<Longrightarrow> \<not> x \<triangleleft> z"
text_raw \<open>}\<close>

context inherence_base
begin

lemma inherence_scope: \<open>x \<triangleleft> y \<Longrightarrow> x \<in> \<E> \<and> y \<in> \<E>\<close>
  using ed_scope inherence_imp_ed by blast

lemma asymm_imp_irrefl:
  assumes \<open>\<And>x y. x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close>
  shows \<open>\<And>x. \<not> x \<triangleleft> x\<close>
  using assms by metis

lemma asymm_imp_antitrgansitivity: 
  assumes \<open>\<And>x y. x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close> \<open>x \<triangleleft> y\<close> \<open>y \<triangleleft> z\<close>
  shows \<open>\<not> x \<triangleleft> z\<close>
proof
  assume \<open>x \<triangleleft> z\<close>
  then have \<open>y = z\<close> using moment_non_migration assms(2) by blast
  then have \<open>z \<triangleleft> z\<close> using assms(3) by blast
  then show False using assms(1) asymm_imp_irrefl by simp
qed

end

text_raw \<open>\Copy{locale:inherence-simplified}{\<close>
locale inherence_simplified =
  inherence_base +
  assumes
    inherence_asymm: \<open>x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close> 
text_raw \<open>}\<close>

sublocale inherence_simplified \<subseteq> inherence_original
proof (unfold_locales)
  show inherence_scope: \<open>\<And>x y. x \<triangleleft> y \<Longrightarrow> x \<in> \<E> \<and> y \<in> \<E>\<close>
    using ed_scope inherence_imp_ed by blast
  show inherence_irrefl: \<open>\<And>x. \<not> x \<triangleleft> x\<close>
    using asymm_imp_irrefl inherence_asymm by metis
  show  \<open>\<And>x y. x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close>
    using inherence_asymm by metis
  show \<open>\<And>x y z. x \<triangleleft> y \<Longrightarrow> y \<triangleleft> z \<Longrightarrow> \<not> x \<triangleleft> z\<close>
    using inherence_asymm asymm_imp_antitrgansitivity by metis
qed

lemma inherence_original_eq_simplified: 
  \<open>inherence_original = inherence_simplified\<close>
proof (intro ext iffI)
  fix \<W> :: \<open>'e set set\<close> and
      inheresIn :: \<open>'e \<Rightarrow> 'e \<Rightarrow> bool\<close> (infix \<open>\<triangleleft>\<close> 75) 
  assume \<open>inherence_original \<W> (\<triangleleft>)\<close>
  then interpret inherence_original \<W> \<open>(\<triangleleft>)\<close> .
  show \<open>inherence_simplified \<W> (\<triangleleft>)\<close>
    apply (unfold_locales)
    using inherence_asymm .  
next
  fix \<W> :: \<open>'e set set\<close> and
      inheresIn :: \<open>'e \<Rightarrow> 'e \<Rightarrow> bool\<close> (infix \<open>\<triangleleft>\<close> 75)
  assume \<open>inherence_simplified \<W> (\<triangleleft>)\<close>
  then interpret inherence_simplified \<W> \<open>(\<triangleleft>)\<close> .
  show \<open>inherence_original \<W> (\<triangleleft>)\<close>
    by intro_locales
qed

text_raw \<open>\Copy{lemma:inherence-original-eq-simplified}{%\<close>
text \<open>@{thm inherence_original_eq_simplified}\<close>
text_raw \<open>}\<close>

context inherence_sig
begin

text_raw \<open>\Copy{def:inherence-symbols}{\<close>
definition \<open>\<M> \<equiv> { x | x y . inheresIn x y }\<close>

definition \<open>\<S> \<equiv> { x . x \<in> \<E> \<and> (\<forall>y. \<not> inheresIn x y) }\<close>

definition \<open>bearerOf s m \<equiv> (\<triangleleft>)\<inverse>\<inverse>\<close>

definition \<open>ultimate_bearer_of s m \<equiv> s \<in> \<S> \<and> m \<in> \<E> \<and> (\<triangleleft>)\<^sup>*\<^sup>* m s\<close>

definition \<open>order_of x n \<equiv> x \<in> \<E> \<and> (\<exists>s \<in> \<S>. ((\<triangleleft>)^^n) x s)\<close> 
text_raw \<open>}\<close> 

definition \<open>has_ultimate_bearer_problem \<equiv> \<exists>x \<in> \<M>. \<nexists>y. ultimate_bearer_of y x\<close>

definition \<open>has_order_problem \<equiv> \<exists>x \<in> \<M>. \<nexists>n. order_of x n\<close>

end

context inherence_sig
begin

lemma \<M>_I[intro]: \<open>x \<triangleleft> y \<Longrightarrow> x \<in> \<M>\<close>
  by (auto simp: \<M>_def)

lemma \<M>_E[elim]:
  assumes \<open>x \<in> \<M>\<close>
  obtains y where \<open>x \<triangleleft> y\<close>
  using assms by (auto simp: \<M>_def)

lemma \<S>_I[intro!]: 
  assumes \<open>x \<in> \<E>\<close> \<open>\<forall>y. \<not> x \<triangleleft> y\<close> 
  shows \<open>x \<in> \<S>\<close>
  using assms by (auto simp: \<S>_def)

lemma \<S>_E[elim]: 
  assumes \<open>x \<in> \<S>\<close>
  obtains \<open>x \<in> \<E>\<close> \<open>\<And>y. x \<triangleleft> y \<Longrightarrow> False\<close>
  using assms by (auto simp: \<S>_def)

lemma \<E>_cases[cases set]:
  assumes \<open>x \<in> \<E>\<close>
  obtains (substantial) \<open>x \<in> \<S>\<close> |
          (moment) \<open>x \<in> \<M>\<close>
  using assms by auto

lemma \<M>_\<S>_disj[dest!]: 
  assumes \<open>x \<in> \<M>\<close> \<open>x \<in> \<S>\<close>
  shows False
  using assms \<M>_E by auto

lemma ultimate_bearer_of_I1:
  assumes \<open>s \<in> \<S>\<close> \<open>m \<in> \<E>\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* m s\<close>
  shows \<open>ultimate_bearer_of s m\<close>
  using assms by (auto simp: ultimate_bearer_of_def)

lemma ultimate_bearer_of_E[elim!]:
  assumes \<open>ultimate_bearer_of s m\<close>
  obtains \<open>s \<in> \<S>\<close> \<open>m \<in> \<E>\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* m s\<close>
  using assms by (auto simp: ultimate_bearer_of_def)

lemma order_of_I1: 
  assumes \<open>x \<in> \<E>\<close> \<open>s \<in> \<S>\<close> \<open>((\<triangleleft>)^^n) x s\<close>
  shows \<open>order_of x n\<close>
  using assms by (auto simp: order_of_def)

lemma order_of_E[elim]: 
  assumes \<open>order_of x n\<close>
  obtains s where \<open>x \<in> \<E>\<close> \<open>s \<in> \<S>\<close> \<open>((\<triangleleft>)^^n) x s\<close>
  using assms by (auto simp: order_of_def)

lemma has_ultimate_bearer_problem_I1:
  assumes \<open>x \<in> \<M>\<close> \<open>\<forall>y. \<not> ultimate_bearer_of y x\<close>
  shows \<open>has_ultimate_bearer_problem\<close>
  using assms apply (simp add: has_ultimate_bearer_problem_def)
  by (intro bexI[of _ x] ; simp)

lemma has_ultimate_bearer_problem_E[elim!]:
  assumes \<open>has_ultimate_bearer_problem\<close>
  obtains x where \<open>x \<in> \<M>\<close> \<open>\<forall>y. \<not> ultimate_bearer_of y x\<close>
  using assms apply (simp add: has_ultimate_bearer_problem_def Bex_def)
  by metis

lemma has_order_problem_I1:
  assumes \<open>x \<in> \<M>\<close> \<open>\<forall>n. \<not> order_of x n\<close>
  shows \<open>has_order_problem\<close>
  using assms apply (simp add: has_order_problem_def)
  by (intro bexI[of _ x] ; simp)

lemma has_order_problem_E[elim!]:
  assumes \<open>has_order_problem\<close>
  obtains x where \<open>x \<in> \<M>\<close> \<open>\<forall>n. \<not> order_of x n\<close>
  using assms apply (simp add: has_order_problem_def Bex_def)
  by metis

end

context inherence_base
begin

lemma \<M>_are_\<E>[dest]: \<open>x \<in> \<M> \<Longrightarrow> x \<in> \<E>\<close>
  using inherence_scope
  by (auto simp: \<M>_def)

lemma ultimate_bearer_of_I[intro!]:
  assumes \<open>s \<in> \<S>\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* m s\<close>
  shows \<open>ultimate_bearer_of s m\<close>
proof -
  have s_E[simp]: \<open>s \<in> \<E>\<close> using \<open>s \<in> \<S>\<close> by blast
  have m_E[simp]: \<open>m \<in> \<E>\<close>
  proof (cases \<open>m = s\<close>)
    case True
    then show ?thesis using \<open>s \<in> \<E>\<close> by simp
  next
    case False
    then have \<open>(\<triangleleft>)\<^sup>+\<^sup>+ m s\<close> 
      using assms by (meson rtranclpD)
    then show ?thesis
      using inherence_scope
      by (meson tranclpD)
  qed
  show ?thesis    
    using assms by (intro ultimate_bearer_of_I1 ; simp)
qed

lemma order_of_I[intro]: 
  assumes \<open>s \<in> \<S>\<close> \<open>((\<triangleleft>)^^n) x s\<close>
  shows \<open>order_of x n\<close>
proof -
  have s_E[simp]: \<open>s \<in> \<E>\<close> using \<open>s \<in> \<S>\<close> by blast
  have m_E[simp]: \<open>x \<in> \<E>\<close>
  proof (cases \<open>x = s\<close>)
    case True
    then show ?thesis using \<open>s \<in> \<E>\<close> by simp
  next
    case False
    then have \<open>(\<triangleleft>)\<^sup>+\<^sup>+ x s\<close> 
      using assms 
      by (meson relpowp_imp_rtranclp rtranclpD)
    then show ?thesis
      using inherence_scope
      by (meson tranclpD)
  qed
  show ?thesis
    by (intro order_of_I1[of _ s] assms ; simp)
qed

lemma has_ultimate_bearer_problem_I[intro]:
  assumes \<open>x \<in> \<E>\<close> \<open>\<forall>y. \<not> ultimate_bearer_of y x\<close>
  shows \<open>has_ultimate_bearer_problem\<close>
proof -
  have \<open>x \<notin> \<S>\<close> using assms(2) ultimate_bearer_of_I by auto
  then have \<open>x \<in> \<M>\<close> using assms(1) by blast
  then show ?thesis
    using assms has_ultimate_bearer_problem_I1 by metis
qed

lemma has_order_problem_I[intro]:
  assumes \<open>x \<in> \<E>\<close> \<open>\<forall>n. \<not> order_of x n\<close>
  shows \<open>has_order_problem\<close>
proof -
  have \<open>x \<notin> \<S>\<close> using assms(2) order_of_I[of x 0] by auto
  then have \<open>x \<in> \<M>\<close> using assms(1) by blast
  then show ?thesis
    using assms has_order_problem_I1 by metis
qed

end

sublocale inherence_simplified \<subseteq> inh: single_valued_range_relation \<open>(\<triangleleft>)\<close>
  apply (unfold_locales)
  using moment_non_migration by metis


context inherence_simplified
begin

lemma ultimate_bearer_iff_ub: \<open>ultimate_bearer_of s m \<longleftrightarrow> m \<in> \<E> \<and> inh.is_upper_bound_of s m\<close>
  apply (auto)  
  by (metis \<E>_I inherence_scope rtranclp.cases)

lemma ub_iff_ultimate_bearer: 
        \<open>inh.is_upper_bound_of s m \<longleftrightarrow> 
         ultimate_bearer_of s m \<or> (m \<notin> \<E> \<and> s = m)\<close>
  apply (auto)
  subgoal for w by (metis \<E>_I inherence_scope rtranclp.cases)
  subgoal by (metis inherence_scope rtranclp.cases)
  by (metis inherence_scope)  

lemma order_of_iff_upper_order_of:
  \<open>order_of x n \<longleftrightarrow> x \<in> \<E> \<and> inh.is_upper_order_of n x\<close>
  apply (auto ; (elim order_of_E inh.is_upper_order_of_E)?)
  subgoal using order_of_I by auto  
  by (metis \<E>_I inherence_scope inherence_sig.\<S>_I 
            order_of_I relpowp_imp_rtranclp rtranclp.cases) 

lemma upper_order_of_iff_order_of:
  \<open>inh.is_upper_order_of n x \<longleftrightarrow> order_of x n \<or> (x \<notin> \<E> \<and> n = 0)\<close>
  apply (auto)
  subgoal by (simp add: \<E>_I order_of_iff_upper_order_of)
  subgoal by (metis inh.is_upper_order_of_def inherence_scope 
                    order_of_iff_upper_order_of relpowp_E2) 
  subgoal by (simp add: order_of_iff_upper_order_of)  
  using inh.is_upper_order_of_def inherence_scope by auto

lemma ultimate_bearer_order_ex_iff:
  \<open>(\<exists>y. ultimate_bearer_of y x) \<longleftrightarrow> (\<exists>n. order_of x n)\<close>
proof (intro iffI ; elim exE ultimate_bearer_of_E order_of_E)
  show \<open>\<exists>n. order_of x n\<close> if as: \<open>y \<in> \<S>\<close> \<open>x \<in> \<E>\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> for x y    
    by (meson order_of_I1 rtranclp_imp_relpowp that) 
  show \<open>\<exists>y. ultimate_bearer_of y x\<close> if as: \<open>x \<in> \<E>\<close> \<open>s \<in> \<S>\<close> \<open>((\<triangleleft>) ^^ n) x s\<close> for n s    
    by (meson relpowp_imp_rtranclp that(2) that(3) ultimate_bearer_of_I)
qed

lemma all_if_not_ex: \<open>(\<forall>x. \<not> P x) \<longleftrightarrow> \<not>(\<exists>x. P x)\<close>  by blast

lemma ultimate_bearer_prob_imp_order_prob:
  \<open>has_ultimate_bearer_problem \<longleftrightarrow> has_order_problem\<close>    
  by (simp add: has_ultimate_bearer_problem_def has_order_problem_def ; 
         simp only: all_if_not_ex ultimate_bearer_order_ex_iff)

lemma \<open>x \<in> \<M> \<Longrightarrow> \<exists>y. ultimate_bearer_of y x\<close>
  nitpick[expect=genuine]
  oops

end

definition 
  \<open>inherence_simplified_model \<Gamma> =
    inherence_simplified (im_\<W> \<Gamma>) (im_inheresIn \<Gamma>) \<close>

context
begin

definition \<open>prob_model_1 \<equiv> \<lparr>
    im_\<W> = { \<emptyset>, {0,1,2} },
    im_inheresIn = (\<lambda>x y. x < 3 \<and> y < 3 \<and> (y = Suc x \<or> x = 2 \<and> y = 0))
  \<rparr>\<close>

abbreviation pm1_worlds (\<open>\<W>\<close>) where \<open>\<W> \<equiv> im_\<W> prob_model_1\<close>

abbreviation inheresIn (infix \<open>\<triangleleft>\<close> 75)
  where \<open>(\<triangleleft>) \<equiv> im_inheresIn prob_model_1\<close>

interpretation  inherence_sig \<open>\<W>\<close> \<open>(\<triangleleft>)\<close> .

lemma prob_model_is_inherence_simplified_model:
  \<open>inherence_simplified_model prob_model_1\<close>
  apply (simp only: inherence_simplified_model_def)
  apply (unfold_locales ; (simp add: ed_def)? ; (simp add: existsIn_def \<E>_def)?
                        ; (simp add: prob_model_1_def)?)
  subgoal for x y
    by (cases x ; cases y ; simp)
  subgoal for x y z
    by (cases x ; cases y ; cases z ; simp)
  subgoal for x y
    by (cases x ; cases y ; simp)
  done

interpretation inherence_simplified \<W> \<open>(\<triangleleft>)\<close>
  using prob_model_is_inherence_simplified_model 
  by (simp add: inherence_simplified_model_def)

lemma prob_model_1_has_ultimate_bearer_problem:
  \<open>has_ultimate_bearer_problem\<close>
proof -
  have \<open>\<S> = \<emptyset>\<close>
  proof (rule ccontr) 
    assume \<open>\<S> \<noteq> \<emptyset>\<close>
    then obtain x where \<open>x \<in> \<S>\<close> by blast
    then obtain A: \<open>x \<in> \<E>\<close> \<open>\<And>y. \<not> x \<triangleleft> y\<close> by blast
    then show False
      apply (cases x ; simp add: \<S>_def \<M>_def \<E>_def 
              ; simp add: prob_model_1_def possible_worlds_alt_sig.\<E>_def)
      subgoal by (elim disjE ; simp ; presburger)
      by presburger
  qed
  show ?thesis
  proof (intro has_ultimate_bearer_problem_I[of 0])
    show \<open>0 \<in> \<E>\<close> by (simp only: \<E>_def ; simp add: prob_model_1_def)
    show \<open>\<forall>y. \<not> ultimate_bearer_of y 0\<close>
    proof (intro allI notI)
      fix y
      assume \<open>ultimate_bearer_of y 0\<close>
      then obtain \<open>y \<in> \<S>\<close> by blast
      then show False using \<open>\<S> = \<emptyset>\<close> by auto
    qed
  qed
qed

no_notation pm1_worlds (\<open>\<W>\<close>) 

no_notation inheresIn (infix \<open>\<triangleleft>\<close> 75)

end

text_raw \<open>\Copy{locale:inherence-with-ultimate-bearers}{%\<close>
locale inherence_with_ultimate_bearers =
  inherence_simplified +
assumes
  ultimate_bearers_ex: 
  \<open>x \<in> \<M> \<Longrightarrow> \<exists>y. ultimate_bearer_of y x\<close>
text_raw \<open>}\<close>

lemma (in inherence_with_ultimate_bearers)
    \<open>\<not> has_ultimate_bearer_problem\<close>
  using has_ultimate_bearer_problem_E ultimate_bearers_ex by metis

text_raw \<open>\Copy{locale:inherence-acyclic}{%\<close>
locale inherence_acyclic =
  inherence_simplified +
 assumes
  acyclic_inherence: \<open>\<not> ((\<triangleleft>)\<^sup>+\<^sup>+) x x\<close>
text_raw \<open>}\<close>

sublocale inherence_with_ultimate_bearers \<subseteq>  
  inh: single_valued_range_upper_bounded_relation \<open>(\<triangleleft>)\<close>
  apply (unfold_locales)
proof -
  fix x
  show \<open>\<exists>y. inh.is_upper_bound_of y x\<close> (is \<open>\<exists>x. ?P x\<close>)
  proof (cases \<open>x \<in> \<M>\<close>)
    assume \<open>x \<notin> \<M>\<close>
    then have \<open>\<not> x \<triangleleft> y\<close> for y by auto
    then show \<open>\<exists>x. ?P x\<close> by blast
  next
    assume \<open>x \<in> \<M>\<close>
    then obtain y where \<open>ultimate_bearer_of y x\<close>
      using ultimate_bearers_ex by metis
    then show \<open>\<exists>x. ?P x\<close>
      by blast
  qed
qed

sublocale inherence_with_ultimate_bearers \<subseteq> inherence_acyclic
  apply (unfold_locales)  
  by (simp add: inh.acyclic)

lemma prob_model_1_not_acyclic:
  \<open>\<not> inherence_acyclic (im_\<W> prob_model_1) (im_inheresIn prob_model_1)\<close>
proof -
  have A: \<open>im_inheresIn prob_model_1 0 1\<close>
          \<open>im_inheresIn prob_model_1 1 2\<close>
          \<open>im_inheresIn prob_model_1 2 0\<close>
    by (simp_all add: prob_model_1_def)
  then have B: \<open>(im_inheresIn prob_model_1)\<^sup>+\<^sup>+ 0 0\<close>
    by auto  
  show ?thesis
  proof 
    assume \<open>inherence_acyclic (im_\<W> prob_model_1) 
                         (im_inheresIn prob_model_1)\<close>
    then interpret inherence_acyclic 
          \<open>im_\<W> prob_model_1\<close> \<open>im_inheresIn prob_model_1\<close> by simp
    show False 
      using B acyclic_inherence by metis
  qed
qed

context
begin

definition \<open>
  prob_model_2 \<equiv> \<lparr>
    im_\<W> = { \<emptyset>, UNIV :: nat set},
    im_inheresIn = (\<lambda>x y. y = Suc x)
    \<rparr>\<close>

private abbreviation pm2_worlds (\<open>\<W>\<close>) where \<open>\<W> \<equiv> im_\<W> prob_model_2\<close>

private abbreviation pm2_inheresIn (infix \<open>\<triangleleft>\<close> 75)
  where \<open>(\<triangleleft>) \<equiv> im_inheresIn prob_model_2\<close>

interpretation inherence_sig \<W> \<open>(\<triangleleft>)\<close> .

interpretation possible_worlds_alt \<W>
    by (unfold_locales ; simp add: prob_model_2_def)

interpretation inherence_original 
    \<open>\<W>\<close> \<open>(\<triangleleft>)\<close> 
  by (unfold_locales ; (simp add: ed_def existsIn_def)?
           ; (simp add: \<E>_def)? ; (simp add: prob_model_2_def))

lemma prob_model_2_is_inherence_acyclic[simp]:
  \<open>inherence_acyclic \<W> (\<triangleleft>)\<close>
proof -
  show ?thesis 
    apply (unfold_locales ; auto simp: prob_model_2_def)
    using less_nat_rel by force
qed

interpretation inherence_acyclic \<W> \<open>(\<triangleleft>)\<close> by simp

lemma prob_model_2_has_ultimate_bearer_problem:
    \<open>has_ultimate_bearer_problem\<close>
proof (intro has_ultimate_bearer_problem_I[of 0] allI)
  show \<open>0 \<in> \<E>\<close>
    by (simp only: \<E>_def ; simp add: prob_model_2_def)
  show \<open>\<not> ultimate_bearer_of y 0\<close> for y
  proof
    assume \<open>ultimate_bearer_of y 0\<close>
    then obtain \<open>y \<in> \<S>\<close> \<open>0 \<in> \<E>\<close> \<open>((\<triangleleft>))\<^sup>*\<^sup>* 0 y\<close>
      using ultimate_bearer_of_def[of y 0] by metis
    have \<open>y \<triangleleft> Suc y\<close>
      by (simp add: prob_model_2_def)
    then have \<open>y \<in> \<M>\<close> by blast
    then show False using \<open>y \<in> \<S>\<close> by blast
  qed
qed

no_notation pm2_worlds (\<open>\<W>\<close>) 

no_notation pm2_inheresIn (infix \<open>\<triangleleft>\<close> 75)

end

text_raw \<open>\Copy{locale:inherence-no-infinite-chains}{\<close>
locale inherence_no_infinite_chains =
  inherence_acyclic +
assumes
  no_infinite_up_chains: 
    \<open>\<lbrakk> x \<in> X ; \<forall>y \<in> X. (\<triangleleft>)\<^sup>*\<^sup>* x y ; 
      \<forall>x \<in> X. \<forall>y \<in> X. (\<triangleleft>)\<^sup>*\<^sup>* x y \<or> (\<triangleleft>)\<^sup>*\<^sup>* y x \<rbrakk> \<Longrightarrow> finite X\<close> 
text_raw \<open>}\<close>

sublocale inherence_no_infinite_chains \<subseteq> 
  inh: single_valued_range_acyclic_finite_lb_chains_relation \<open>(\<triangleleft>)\<close>  
proof -
  have fin_lb_chain: \<open>finite X\<close> if \<open>lb_chain (\<triangleleft>) X\<close> for X
  proof -
    interpret P: lb_chain \<open>(\<triangleleft>)\<close> X using that .
    obtain x where x: \<open>x \<in> X\<close> \<open>\<And>y. y \<in> X \<Longrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* x y\<close>      
      using P.lb_exists by blast
    have R1: \<open>\<forall>y \<in> X.(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> using x by auto
    have R2: \<open>\<forall>x \<in> X. \<forall>y \<in> X. (\<triangleleft>)\<^sup>*\<^sup>* x y \<or> (\<triangleleft>)\<^sup>*\<^sup>* y x\<close>
      using P.R_connected by blast
    show \<open>finite X\<close> using no_infinite_up_chains R1 R2 \<open>x \<in> X\<close> by metis
  qed
  
  show \<open>single_valued_range_acyclic_finite_lb_chains_relation (\<triangleleft>)\<close>
    by (unfold_locales ; simp add: moment_non_migration acyclic_inherence fin_lb_chain)    
qed

theorem inherence_acyclic_no_infinite_chains_eq_no_ultimate_bearers:
 \<open>inherence_no_infinite_chains = inherence_with_ultimate_bearers\<close>
proof (intro ext iffI)
  fix \<W> :: \<open>'e set set\<close> and inheresIn (infix \<open>\<triangleleft>\<close> 75)
  assume \<open>inherence_no_infinite_chains \<W> (\<triangleleft>)\<close>
  then interpret inherence_no_infinite_chains \<W> \<open>(\<triangleleft>)\<close> .
  interpret inh: single_valued_range_upper_bounded_relation \<open>(\<triangleleft>)\<close>
    apply (simp only: single_valued_range_acyclic_finite_lb_chains_relation_ub[symmetric])
    by (intro_locales)
  show \<open>inherence_with_ultimate_bearers \<W> (\<triangleleft>)\<close>
  proof (unfold_locales)
    fix x
    assume \<open>x \<in> \<M>\<close>
    then obtain y where \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> \<open>\<And>z. \<not> y \<triangleleft> z\<close>
      using inh.upper_bounded inh.is_upper_bound_of_E by metis
    then have \<open>y \<in> \<E>\<close> using \<open>x \<in> \<M>\<close> 
      by (metis local.\<M>_E local.inherence_scope rtranclp.cases)
    then have \<open>y \<in> \<S>\<close> using \<S>_I \<open>\<And>z. \<not> y \<triangleleft> z\<close> by blast
    have \<open>x \<in> \<E>\<close> using  \<open>x \<in> \<M>\<close> \<M>_E inherence_scope by metis
    have \<open>ultimate_bearer_of y x\<close>
      by (intro ultimate_bearer_of_I \<open>x \<in> \<E>\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> \<open>y \<in> \<S>\<close>)
    then show \<open>\<exists>y. local.ultimate_bearer_of y x\<close> by metis
  qed
next
  fix \<W> :: \<open>'e set set\<close> and inheresIn (infix \<open>\<triangleleft>\<close> 75)
  assume \<open>inherence_with_ultimate_bearers \<W> (\<triangleleft>)\<close>
  then interpret inherence_with_ultimate_bearers \<W> \<open>(\<triangleleft>)\<close> .   
  interpret inh: single_valued_range_upper_bounded_relation \<open>(\<triangleleft>)\<close>
    by unfold_locales
  interpret inh: single_valued_range_acyclic_finite_lb_chains_relation \<open>(\<triangleleft>)\<close>
    apply (simp only: single_valued_range_acyclic_finite_lb_chains_relation_ub)
    by intro_locales
  show \<open>inherence_no_infinite_chains \<W> (\<triangleleft>)\<close>
  proof (unfold_locales)
    show \<open>finite X\<close> 
        if as: \<open>x \<in> X\<close> \<open>\<forall>y\<in>X. (\<triangleleft>)\<^sup>*\<^sup>* x y\<close> 
               \<open>\<forall>x\<in>X. \<forall>y\<in>X. (\<triangleleft>)\<^sup>*\<^sup>* x y \<or> (\<triangleleft>)\<^sup>*\<^sup>* y x\<close> 
             for x X
      apply (intro inh.finite_lb_chains ; unfold_locales)
      using as by auto
  qed
qed

text_raw \<open>\Copy{locale:inherence-noetherian}{\<close>
locale inherence_noetherian =
  inherence_base  +
    assumes
    inherence_is_noetherian: \<open>wfP ((\<triangleleft>)\<inverse>\<inverse>)\<close>
text_raw \<open>}\<close>

context inherence_base
begin
text_raw \<open>\Copy{def:wfP-eq-minimal-bearer-of}{%\<close> text \<open>@{thm wfP_eq_minimal[of \<open>(\<triangleleft>)\<inverse>\<inverse>\<close>,simplified]}\<close> text_raw \<open>}\<close>
end

sublocale inherence_noetherian \<subseteq>
   inh: single_valued_range_noetherian_relation \<open>(\<triangleleft>)\<close>
  using moment_non_migration inherence_is_noetherian
    by (unfold_locales ; metis)

theorem noethereian_inherence_eq_inherence_with_ultimate_bearers:
  \<open>inherence_noetherian = inherence_with_ultimate_bearers\<close>
proof (intro ext iffI)
  fix \<W> :: \<open>'e set set\<close> and inheresIn (infix \<open>\<triangleleft>\<close> 75)
  assume \<open>inherence_noetherian \<W> (\<triangleleft>)\<close>
  then interpret inherence_noetherian \<W> \<open>(\<triangleleft>)\<close> .  
  interpret inh: single_valued_range_noetherian_relation \<open>(\<triangleleft>)\<close>
    by intro_locales
  interpret inh: single_valued_range_upper_bounded_relation \<open>(\<triangleleft>)\<close>
    using single_valued_range_ub_eq_noetherian 
    by auto
  show \<open>inherence_with_ultimate_bearers \<W> (\<triangleleft>)\<close>
  proof (unfold_locales)
    show asymm: \<open>\<not> y \<triangleleft> x\<close> if \<open>x \<triangleleft> y\<close> for x y 
      by (meson inh.acyclic r_into_rtranclp rtranclp_into_tranclp1 that) 
    show \<open>\<exists>y. ultimate_bearer_of y x\<close> if \<open>x \<in> \<M>\<close> for x
      by (metis \<M>_are_\<E> \<open>\<And>y x. x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close> 
          inh.all_unique_upper_order inherence_base_axioms
          inherence_simplified.order_of_iff_upper_order_of
          inherence_simplified.ultimate_bearer_order_ex_iff 
          inherence_simplified_axioms.intro inherence_simplified_def 
          that) 
  qed
next
  fix \<W> :: \<open>'e set set\<close> and inheresIn (infix \<open>\<triangleleft>\<close> 75)
  assume \<open>inherence_with_ultimate_bearers \<W> (\<triangleleft>)\<close>
  then interpret inherence_with_ultimate_bearers \<W> \<open>(\<triangleleft>)\<close> .
  interpret inh: single_valued_range_upper_bounded_relation \<open>(\<triangleleft>)\<close>
    by (unfold_locales)
  show \<open>inherence_noetherian \<W> (\<triangleleft>)\<close>
    apply (unfold_locales)    
    by (simp add: inh.noetherian)    
qed

context inherence_noetherian
begin

text_raw \<open>\Copy{lemma:noetherian-induct}{\<close>
text \<open>@{thm inherence_is_noetherian[THEN wfP_induct,of P z,simplified]}\<close>
text_raw \<open>}\<close>
end

end
