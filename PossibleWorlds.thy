theory PossibleWorlds
  imports Common
begin

text_raw \<open>\Copy{locale:possible-worlds-original-sig}{\<close>
locale possible_worlds_original_sig =
  fixes 
    \<W> :: \<open>'w set\<close> and
    \<E> :: \<open>'e set\<close> and
    existsIn :: \<open>'e \<Rightarrow> 'w \<Rightarrow> bool\<close>
text_raw \<open>}\<close>

context possible_worlds_original_sig
begin 
 
definition \<open>ed x y \<equiv> x \<in> \<E> \<and> y \<in> \<E> \<and> (\<forall>w \<in> \<W>. existsIn x w \<longrightarrow> existsIn y w)\<close>

text_raw\<open>\Copy{def:possible-worlds-original-sig.extensionOf}{%\<close>
definition \<open>extensionOf w \<equiv> { x . existsIn x w }\<close>
text_raw\<open>}\<close>

text_raw\<open>\Copy{def:possible-worlds-original-sig.extensions}{%\<close>
definition \<open>extensions \<equiv> { extensionOf w | w . w \<in> \<W> }\<close>
text_raw\<open>}\<close>
end

text_raw \<open>\Copy{exported-def:possible-worlds-original-sig.ed}{\<close>
text \<open>@{thm possible_worlds_original_sig.ed_def}\<close>
text_raw \<open>}\<close>

context possible_worlds_original_sig
begin

text_raw\<open>\Copy{basic-lemmas:possible-worlds-original-sig.ed}{\<close>
lemma edI[intro!]:
  assumes \<open>x \<in> \<E>\<close> \<open>y \<in> \<E>\<close> \<open>\<And>w. \<lbrakk> w \<in> \<W> ; existsIn x w \<rbrakk> \<Longrightarrow> existsIn y w\<close>
  shows \<open>ed x y\<close>
  using assms
  by (auto simp: ed_def)

lemma edE[elim]:
  assumes \<open>ed x y\<close> \<open>w \<in> \<W>\<close> \<open>existsIn x w\<close>
  obtains \<open>x \<in> \<E>\<close> \<open>y \<in> \<E>\<close> \<open>\<And>w. \<lbrakk> w \<in> \<W> ; existsIn x w \<rbrakk> \<Longrightarrow> existsIn y w\<close>
  using assms
  by (auto simp: ed_def)
text_raw\<open>}\<close>

lemma edD[dest]:
  assumes \<open>ed x y\<close> \<open>w \<in> \<W>\<close> \<open>existsIn x w\<close>
  shows \<open>existsIn y w\<close>
  using assms
  by (auto simp: ed_def)

lemma ed_scope[dest]:
  assumes \<open>ed x y\<close>
  shows \<open>x \<in> \<E>\<close> \<open>y \<in> \<E>\<close>
  using assms by (auto simp: ed_def)

text_raw \<open>\Copy{lemmas:ed-preorder}{\<close>
lemma ed_transitive: \<open>\<lbrakk> ed x y ; ed y z \<rbrakk> \<Longrightarrow> ed x z\<close> by auto

lemma ed_reflexive: \<open>x \<in> \<E> \<Longrightarrow> ed x x\<close> by auto  
text_raw \<open>}\<close>

lemma extension_iff[iff]: 
    \<open>x \<in> extensionOf w \<longleftrightarrow> existsIn x w\<close>
  by (auto simp: extensionOf_def)

lemma extensions_iff[iff]:
  \<open>s \<in> extensions \<longleftrightarrow> (\<exists>w. w \<in> \<W> \<and> s = extensionOf w)\<close> 
  by (auto simp: extensions_def)

lemma extensionOf_bij_I:
  assumes \<open>\<forall>w\<^sub>1 \<in> \<W>. \<forall>w\<^sub>2 \<in> \<W>. (\<forall>x. existsIn x w\<^sub>1 \<longleftrightarrow> existsIn x w\<^sub>2) \<longrightarrow> w\<^sub>1 = w\<^sub>2\<close> 
  shows \<open>bij_betw extensionOf \<W> extensions\<close>
proof -
  have A: \<open>extensionOf ` \<W> = extensions\<close> by auto
  have B: \<open>inj_on extensionOf \<W>\<close>
  proof
    fix w\<^sub>1 w\<^sub>2
    assume as: \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w\<^sub>2 \<in> \<W>\<close> \<open>extensionOf w\<^sub>1 = extensionOf w\<^sub>2\<close>
    show \<open>w\<^sub>1 = w\<^sub>2\<close> when \<open>\<forall>x. existsIn x w\<^sub>1 \<longleftrightarrow> existsIn x w\<^sub>2\<close> 
      using assms as(1,2) that by simp
    show \<open>\<forall>x. existsIn x w\<^sub>1 \<longleftrightarrow> existsIn x w\<^sub>2\<close>
      using extension_iff as(3) by auto
  qed
  show ?thesis using A B 
    by (simp add: bij_betw_def)
qed

end

text_raw \<open>\Copy{locale:possible-worlds-original}{\<close>
locale possible_worlds_original = 
  possible_worlds_original_sig +
assumes
  existence_scope:
  \<open>existsIn x w \<Longrightarrow> 
      w \<in> \<W> \<and> x \<in> \<E>\<close> 
and endurants_exist_somewhere:
  \<open>x \<in> \<E> \<Longrightarrow> \<exists>w. existsIn x w\<close> 
and world_equality: 
  \<open>\<lbrakk> w\<^sub>1 \<in> \<W> ; w\<^sub>2 \<in> \<W> ; 
   \<forall>x. existsIn x w\<^sub>1 \<longleftrightarrow> existsIn x w\<^sub>2 \<rbrakk> \<Longrightarrow> 
   w\<^sub>1 = w\<^sub>2\<close> 
and endurants_are_contingent: 
   \<open>x \<in> \<E> \<Longrightarrow> 
    \<exists>w \<in> \<W>. \<not> existsIn x w\<close> 
and at_least_one_possible_world: 
   \<open>\<W> \<noteq> \<emptyset>\<close>
text_raw \<open>}\<close>

context possible_worlds_original
begin


lemma endurants_are_the_existents[simp]: 
 \<open>x \<in> \<E> \<longleftrightarrow> (\<exists>w. existsIn x w)\<close>
using existence_scope
      endurants_exist_somewhere
by auto

lemma extension_of_is_a_bijection: 
  \<open>bij_betw extensionOf \<W> extensions\<close>
proof -
  have surj: \<open>extensions = extensionOf ` \<W>\<close>
    by auto
  have inj: \<open>w\<^sub>1 = w\<^sub>2\<close> 
    if \<open>w\<^sub>1 \<in> \<W>\<close> \<open>w\<^sub>2 \<in> \<W>\<close> \<open>extensionOf w\<^sub>1 = extensionOf w\<^sub>2\<close> 
    for w\<^sub>1 w\<^sub>2
    using that world_equality by auto
  show ?thesis
    using surj inj 
    by (simp add: bij_betw_def inj_on_def)
qed

lemma endurants_are_union_of_extensions: \<open>\<E> = \<Union> extensions\<close>
proof -
  obtain f where f: \<open>\<And>x. x \<in> \<E> \<Longrightarrow> f x \<in> \<W>\<close> \<open>\<And>x. x \<in> \<E> \<Longrightarrow> existsIn x (f x)\<close>
    using that 
    by (metis endurants_exist_somewhere existence_scope)
  show ?thesis when
    \<open>\<And>x. x \<in> \<E> \<Longrightarrow> \<exists>s. s \<in> extensions \<and> x \<in> s\<close>
    \<open>\<And>s. s \<in> extensions \<Longrightarrow> s \<subseteq> \<E>\<close>
    apply (intro set_eqI iffI ; (elim UnionE)?)
    subgoal for x      
      apply (intro UnionI[of \<open>extensionOf (f x)\<close>] ; frule f(1) ; frule f(2))
      by auto
    by auto
  show \<open>\<exists>s. s \<in> extensions \<and> x \<in> s\<close> if \<open>x \<in> \<E>\<close> for x
    using that f by auto
  show \<open>s \<subseteq> \<E>\<close> if \<open>s \<in> extensions\<close> for s using that by auto
qed

text_raw\<open>\Copy{lemma:possible-worlds-original.endurants-are-union-of-extensions}{%\<close>
text \<open>@{thm endurants_are_union_of_extensions}%\<close>
text_raw\<open>}\<close>


lemma existence_corresponds_to_extension_membership:  
  \<open>existsIn x w \<longleftrightarrow> w \<in> \<W> \<and> x \<in> extensionOf w\<close>  
  using existence_scope by blast

text_raw\<open>\Copy{lemma:possible-worlds-original.existence-corresponds-to-extension-membership}{\<close>
text \<open>@{thm existence_corresponds_to_extension_membership[of x w]}\<close>
text_raw\<open>}\<close>


end

text_raw \<open>\Copy{locale:possible-worlds-alt-sig}{\<close>
locale possible_worlds_alt_sig =
  fixes  \<W> :: \<open>'e set set\<close>
text_raw \<open>}\<close>

context possible_worlds_alt_sig
begin
text_raw \<open>\Copy{definition:possible-worlds-alt-sig.existsIn}{\<close>
definition \<open>existsIn x w \<equiv> w \<in> \<W> \<and> x \<in> w\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{definition:possible-worlds-alt-sig.endurants}{\<close>
definition \<open>\<E> \<equiv> { x . \<exists>w \<in> \<W>. x \<in> w }\<close>
text_raw \<open>}\<close>

lemma existsIn_I[intro!]: 
  assumes \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  shows \<open>existsIn x w\<close>
  using assms
  by (auto simp: existsIn_def)

lemma existsIn_E[elim!]: 
  assumes \<open>existsIn x w\<close>
  obtains \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  using assms
  by (auto simp: existsIn_def)

lemma \<E>_I[intro]:
  assumes \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  shows \<open>x \<in> \<E>\<close>
  using assms
  by (auto simp: \<E>_def)

lemma \<E>_E[elim!]:
  assumes \<open>x \<in> \<E>\<close>
  obtains w where \<open>w \<in> \<W>\<close> \<open>x \<in> w\<close>
  using assms
  by (auto simp: \<E>_def)

end

sublocale possible_worlds_alt_sig \<subseteq> 
    possible_worlds_original_sig where \<W> = \<W> and \<E> = \<E> and existsIn = existsIn .

text_raw \<open>\Copy{locale:possible-worlds-alt}{\<close>
locale possible_worlds_alt =
  possible_worlds_alt_sig +
assumes
    world_set_intersection_empty: \<open>\<Inter> \<W> = \<emptyset>\<close> 
and at_least_one_possible_world: \<open>\<W> \<noteq> \<emptyset>\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{record:possible-worlds-original-model}{\<close>
record ('e,'w) possible_worlds_original_model =
  pw_1_\<E> :: \<open>'e set\<close>
  pw_1_\<W> :: \<open>'w set\<close>
  pw_1_existsIn :: \<open>'e \<Rightarrow> 'w \<Rightarrow> bool\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{type-synonym:possible-worlds-alt-model}{\<close>
type_synonym 'e possible_worlds_alt_model = \<open>'e set set\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{definition:PW1-Models}{\<close>
definition \<open>PW1_Models \<equiv>
  { \<Gamma> . possible_worlds_original (pw_1_\<W> \<Gamma>) (pw_1_\<E> \<Gamma>) (pw_1_existsIn \<Gamma>) }\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{definition:PW2-Models}{\<close>
definition \<open>PW2_Models \<equiv> { \<W> . possible_worlds_alt \<W> }\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{definition:pw1-to-pw2}{\<close>
definition pw1_to_pw2 
        :: \<open>('e,'w) possible_worlds_original_model \<Rightarrow> 
            'e possible_worlds_alt_model\<close> where
  \<open>pw1_to_pw2 \<Gamma> \<equiv> 
    possible_worlds_original_sig.extensions 
       (pw_1_\<W> \<Gamma>) (pw_1_existsIn \<Gamma>)\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{definition:pw2-to-pw1}{\<close>
definition pw2_to_pw1 ::
  \<open>('e set \<Rightarrow> 'w) \<Rightarrow> 'e set set \<Rightarrow>  
    ('e,'w) possible_worlds_original_model \<close> where
 \<open>pw2_to_pw1 f \<Gamma> \<equiv> \<lparr>
    pw_1_\<E> = possible_worlds_alt_sig.\<E> \<Gamma>,
    pw_1_\<W> = f ` \<Gamma>,
    pw_1_existsIn = (\<lambda>x w. w \<in> f ` \<Gamma> \<and> 
                           x \<in> inv_into \<Gamma> f w)
    \<rparr>\<close>
text_raw \<open>}\<close>

lemma pw1_to_pw2:
  fixes \<Gamma> :: \<open>('e,'w) possible_worlds_original_model\<close>
  assumes \<open>\<Gamma> \<in> PW1_Models\<close>
  shows \<open>pw1_to_pw2 \<Gamma> \<in> PW2_Models\<close>
proof -  
  interpret possible_worlds_original \<open>pw_1_\<W> \<Gamma>\<close> \<open>pw_1_\<E> \<Gamma>\<close> \<open>pw_1_existsIn \<Gamma>\<close> 
    using assms by (auto simp: PW1_Models_def)

  have R1: \<open>\<Inter> extensions = \<emptyset>\<close>
  proof (auto)
    fix x
    assume as: \<open>\<forall>s \<in> extensions. x \<in> s\<close>
    obtain w where \<open>w \<in> pw_1_\<W> \<Gamma>\<close>
      using at_least_one_possible_world by blast
    then have \<open>extensionOf w \<in> extensions\<close> by blast
    then have \<open>pw_1_existsIn \<Gamma> x w\<close> using as by blast
    then have \<open>x \<in> pw_1_\<E> \<Gamma>\<close> 
      using endurants_are_the_existents by blast
    then obtain w\<^sub>1 where \<open>w\<^sub>1 \<in> pw_1_\<W> \<Gamma>\<close> \<open>\<not> pw_1_existsIn \<Gamma> x w\<^sub>1\<close>
      using endurants_are_contingent by blast
    then obtain \<open>extensionOf w\<^sub>1 \<in> extensions\<close> \<open>x \<notin> extensionOf w\<^sub>1\<close>
      by blast
    then show False using as by blast
  qed

  show ?thesis
    apply (simp add: PW2_Models_def pw1_to_pw2_def ; unfold_locales)
    subgoal using R1 .    
    using R1 by force
qed

lemma pw2_to_pw1:
  fixes \<Gamma> :: \<open>'e set set\<close>
        and f :: \<open>'e set \<Rightarrow> 'w\<close>
  assumes f_inj: \<open>inj_on f \<Gamma>\<close> \<open>\<Gamma> \<in> PW2_Models\<close>  
  shows \<open>pw2_to_pw1 f \<Gamma>  \<in> PW1_Models\<close> 
proof -
  let ?\<W> = \<Gamma>
  
  interpret P: possible_worlds_alt \<open>?\<W>\<close> 
    using assms by (simp add: PW2_Models_def)  

  have f_inv_f[simp]: \<open>inv_into (?\<W>) f (f w) = w\<close> if \<open>w \<in> ?\<W>\<close> for w using f_inj    
    by (simp add: that)
  
  show \<open>pw2_to_pw1 f \<Gamma> \<in> PW1_Models\<close>
    apply (simp add: PW1_Models_def pw2_to_pw1_def ; unfold_locales
            ; auto )
    subgoal by (subst (asm) set_eq_iff[symmetric,simp] ; simp)
    subgoal by (metis InterI P.world_set_intersection_empty emptyE)
    using P.at_least_one_possible_world by auto   
qed 

text_raw \<open>\Copy{thm:pw1-to-pw2}{\<close>
text \<open>@{thm pw1_to_pw2}\<close>
text_raw \<open>}\<close>

text_raw \<open>\Copy{thm:pw2-to-pw1}{\<close>
text \<open>@{thm pw2_to_pw1}\<close>
text_raw \<open>}\<close>

  
end

