theory Order_Relations_From_Priorities
  imports 
    Order_Relations
    Treaps.Random_List_Permutation
begin

subsection \<open>Unweighted Case\<close>
lemma preorder_on_linorder_from_keys[intro]: "preorder_on A (linorder_from_keys A f)"
  unfolding linorder_from_keys_def preorder_on_def
  by (auto simp: refl_on_def trans_def total_on_def) 

lemma linorder_from_keys_in_preorders_on[intro]: "linorder_from_keys A f \<in> preorders_on A"
  by auto

lemma linorder_from_keys_lessI:
  assumes "f i < f j"
  assumes "i \<in> A" "j \<in> A"
  shows "(i,j) \<in> linorder_from_keys A f \<and> (j,i) \<notin> linorder_from_keys A f"
  using assms
  unfolding linorder_from_keys_def
  by auto

lemma linorder_from_keys_Restr:
  shows "Restr (linorder_from_keys A f) (A - B) = linorder_from_keys (A - B) f"
  unfolding linorder_from_keys_def
  by blast

lemma linorder_from_keys_update_eq:
  shows "linorder_from_keys (A - {a}) (f(a:=x)) = linorder_from_keys (A - {a}) f"
  unfolding linorder_from_keys_def
  by auto

text \<open>Generalize @{thm measurable_linorder_from_keys_restrict} by Eberl from
 \<^term>\<open>count_space (Pow (A \<times> A))\<close> to \<^term>\<open>count_space (preorders_on A)\<close>. The original
  statement then also follows with @{thm measurable_count_space_extend}.}\<close>
lemma measurable_linorder_from_keys_restrict_preorders[measurable]:
  assumes fin: "finite A"
  shows "linorder_from_keys A \<in> Pi\<^sub>M A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (preorders_on A)"
  (is "_ : ?M \<rightarrow>\<^sub>M _")
  apply (subst measurable_count_space_eq2)
   apply (auto simp: fin)
proof -
  note fin[simp]
  fix r assume "r \<in> preorders_on A"
  then have "linorder_from_keys A -` {r} \<inter> space ?M =
    {f \<in> space ?M. \<forall>x\<in>A. \<forall>y\<in>A. (x,y) \<in> r \<longleftrightarrow> f x \<le> f y}"
    by (auto simp: linorder_from_keys_def preorder_on_def set_eq_iff dest!: preorders_onD refl_on_domain)

  also have "\<dots> \<in> sets ?M"
    by measurable

  finally show "linorder_from_keys A -` {r} \<inter> space ?M \<in> sets ?M" .
qed

subsection \<open>Weighted Case\<close>
definition weighted_linorder_from_keys :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<times> 'a) set" where
  "weighted_linorder_from_keys A v g Y \<equiv> {(x,y) \<in> A \<times> A. v x * (1 - g(Y x)) \<ge> v y * (1 - g(Y y))}"

lemma preorder_on_weighted_linorder_from_keys[intro]: "preorder_on A (weighted_linorder_from_keys A v g f)"
  unfolding weighted_linorder_from_keys_def preorder_on_def
  by (auto simp: refl_on_def trans_def total_on_def) 

lemma weighted_linorder_from_keys_in_preorders_on[intro]: "weighted_linorder_from_keys A v g f \<in> preorders_on A"
  by auto

lemma measurable_weighted_linorder_from_keys[measurable]:
  assumes fin: "finite A"
  assumes "g \<in> borel_measurable borel"
  shows "weighted_linorder_from_keys A v g \<in> PiM A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (preorders_on A)"
  (is "_ \<in> ?M \<rightarrow>\<^sub>M _")
  apply (subst measurable_count_space_eq2)
   apply (auto simp: fin)
proof -
  note fin[simp]
  fix r assume "r \<in> preorders_on A"
  then have "weighted_linorder_from_keys A v g -` {r} \<inter> space ?M =
    {f \<in> space ?M. \<forall>x\<in>A. \<forall>y\<in>A. (x,y) \<in> r \<longleftrightarrow> v x * (1 - g(f x)) \<ge> v y * (1 - g(f y))}"
    by (auto simp: weighted_linorder_from_keys_def preorder_on_def set_eq_iff dest!: preorders_onD refl_on_domain)

  also from assms have "\<dots> \<in> sets ?M"
    by measurable

  finally show "weighted_linorder_from_keys A v g -` {r} \<inter> space ?M \<in> sets ?M" .
qed

lemma weighted_linorder_from_keys_Restr:
  shows "Restr (weighted_linorder_from_keys A v g f) (A - B) = weighted_linorder_from_keys (A - B) v g f"
  unfolding weighted_linorder_from_keys_def
  by blast

lemma weighted_linorder_from_keys_update_eq:
  shows "weighted_linorder_from_keys (A - {a}) v g (f(a:=x)) = weighted_linorder_from_keys (A - {a}) v g f"
  unfolding weighted_linorder_from_keys_def
  by auto

lemma weighted_linorder_from_keys_lessI:
  assumes "v i * (1 - g (f i)) > v j * (1 - g (f j))"
  assumes "i \<in> A" "j \<in> A"
  shows "(i,j) \<in> weighted_linorder_from_keys A v g f \<and> (j,i) \<notin> weighted_linorder_from_keys A v g f"
  using assms
  unfolding weighted_linorder_from_keys_def
  by auto

lemma linorder_on_weighted_linorder_from_keys[intro]:
  assumes "inj_on (\<lambda>a. v a * (1 - g (f a))) A"
  shows "linorder_on A (weighted_linorder_from_keys A v g f)"
  using assms
  by (auto simp: linorder_on_def refl_on_def antisym_def weighted_linorder_from_keys_def trans_def total_on_def
           dest: inj_onD)


end