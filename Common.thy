theory Common
  imports Main "HOL-Library.LaTeXsugar"    
begin

sledgehammer_params [timeout=60,provers= cvc4 vampire z3 e spass]

definition \<open>restrict f X x \<equiv> if x \<in> X then Some (f x) else None\<close>

lemma restrict_dom[simp]: \<open>dom (restrict f X) = X\<close>
  apply (auto simp: restrict_def)
  subgoal for x y
    by (cases \<open>x \<in> X\<close> ; simp)?
  done

lemma restrict_ran[simp]: \<open>ran (restrict f X) = f ` X\<close>
  by (auto simp: restrict_def ran_def)

lemma restrict_in_dom[simp]: \<open>restrict f X x = Some (f x)\<close> if \<open>x \<in> X\<close>
  using that by (auto simp: restrict_def)

lemma restrict_notin_dom[simp]: \<open>restrict f X x = None\<close> if \<open>x \<notin> X\<close>
  using that by (auto simp: restrict_def)

lemma restrict_inj_on[simp]: \<open>inj_on (restrict f X) X \<longleftrightarrow> inj_on f X\<close>
  by (auto intro!: inj_onI elim!: inj_onD)



end
