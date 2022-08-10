theory Ranking_Order_Probabilistic
  imports
    Ranking_Order
    "Treaps.Random_List_Permutation"
begin

lemma linorder_from_keys_preorder[intro]: "linorder_from_keys A f \<in> preorders_on A"
  unfolding linorder_from_keys_def
  by (auto intro!: preorders_onI simp: preorder_on_def refl_on_def trans_def)

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

locale wf_ranking_order_prob = wf_ranking_order +
  fixes \<pi> :: "'a list" and M
  defines "M \<equiv> \<Pi>\<^sub>M i \<in> L. uniform_measure lborel {0..1::real}"

  assumes perm: "\<pi> \<in> permutations_of_set R"
begin

lemma ranking_subgraph:
  assumes "r \<in> preorders_on L"
  shows "ranking r G \<pi> \<subseteq> G"
  using assms perm graph
  by (intro ranking'_subgraph)
     (auto intro: preorder_on_neighborsI ranking'_subgraph dest: permutations_of_setD)

lemma ranking_measurable:
  "(\<lambda>Y. ranking (linorder_from_keys L Y) G \<pi>) \<in> M \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys L" _ "count_space (preorders_on L)" "\<lambda>r. ranking r G \<pi>"], goal_cases)
  case 1
  from finite_L show ?case
    unfolding M_def
    by measurable
next
  case 2
  from finite_subsets show ?case
    by (subst measurable_count_space_eq2)
       (auto dest: ranking_subgraph)
qed



end

end