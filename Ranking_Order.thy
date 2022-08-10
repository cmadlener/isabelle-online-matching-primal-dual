theory Ranking_Order
  imports
    More_Graph
    "Treaps.Random_List_Permutation"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

text \<open>Weaker versions of \<^term>\<open>refl_on\<close> (and \<^term>\<open>linorder_on\<close>) that don't enforce
that the relation is only defined on the given set.\<close>
definition "refl_on' S r \<longleftrightarrow> (\<forall>x\<in>S. (x,x) \<in> r)"
definition "preorder_on' S r \<longleftrightarrow> refl_on' S r \<and> trans r"

definition "preorders_on S \<equiv> {r. preorder_on S r}"

lemma preorders_onD: "r \<in> preorders_on S \<Longrightarrow> preorder_on S r"
  unfolding preorders_on_def
  by blast

lemma preorders_onI: "preorder_on S r \<Longrightarrow> r \<in> preorders_on S"
  unfolding preorders_on_def
  by blast

lemma preorder_on_subset_Times: "preorder_on S r \<Longrightarrow> r \<subseteq> S \<times> S"
  unfolding preorder_on_def
  by (auto dest: refl_onD1 refl_onD2)

lemma preorders_on_subset_Pow: "preorders_on S \<subseteq> Pow (S \<times> S)"
  by (auto dest: preorders_onD preorder_on_subset_Times)

lemma finite_preorders_on[intro]:
  assumes "finite S"
  shows "finite (preorders_on S)"
  using assms
  by (auto intro: finite_subset[OF preorders_on_subset_Pow])

lemma refl_on_imp_refl_on': "refl_on S r \<Longrightarrow> refl_on' S r"
  unfolding refl_on_def refl_on'_def
  by blast

lemma preorder_on_imp_preorder_on': "preorder_on S r \<Longrightarrow> preorder_on' S r"
  unfolding preorder_on_def preorder_on'_def
  by (blast intro: refl_on_imp_refl_on')

lemma refl_on'_subset:
  "refl_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> refl_on' T r"
  unfolding refl_on'_def
  by blast

lemma preorder_on'_subset:
  "preorder_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> preorder_on' T r"
  unfolding preorder_on'_def
  by (auto intro: refl_on'_subset total_on_subset)
  
definition is_min_rel :: "('a \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_min_rel P r x = (P x \<and> \<not>(\<exists>y. P y \<and> (y,x) \<in> r \<and> (x,y) \<notin> r))"

definition min_rel :: "('a \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> 'a" where
  "min_rel P r = (SOME x. is_min_rel P r x)"

definition min_on_rel :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a" where
  "min_on_rel S r = min_rel (\<lambda>x. x \<in> S) r"

lemma ex_min_if_finite:
  "\<lbrakk> finite S; S \<noteq> {}; preorder_on' S r \<rbrakk> \<Longrightarrow> \<exists>m\<in>S. \<not>(\<exists>x\<in>S. (x,m) \<in> r \<and> (m,x) \<notin> r)"
proof (induction arbitrary: r rule: finite.induct)
  case (insertI A a)
  then show ?case
  proof (cases "A \<noteq> {}")
    case True
    from insertI have "preorder_on' A r"
      by (auto intro: preorder_on'_subset)

    with True insertI obtain m where m: "m\<in>A" "\<not>(\<exists>x\<in>A. (x,m) \<in> r \<and> (m,x) \<notin> r)"
      by blast

    with \<open>preorder_on' (insert a A) r\<close> show ?thesis
      unfolding preorder_on'_def
      by (auto dest: transD)
  qed simp
qed simp

lemma ex_is_min_if_finite:
  assumes "preorder_on' S r"
  assumes "finite S" "S \<noteq> {}"
  shows "\<exists>x. is_min_rel (\<lambda>x. x \<in> S) r x"
  using assms
  unfolding is_min_rel_def
  using ex_min_if_finite
  by fast

lemma min_if_finite:
  assumes "preorder_on' S r"
  assumes "finite S" "S \<noteq> {}"
  shows "min_on_rel S r \<in> S" and "\<not>(\<exists>x\<in>S. (x, min_on_rel S r) \<in> r \<and> (min_on_rel S r, x) \<notin> r)"
  using assms
  by (metis ex_is_min_if_finite is_min_rel_def min_on_rel_def min_rel_def some_eq_ex)+

definition step :: "('a \<times> 'a) set \<Rightarrow> 'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a graph" where
  "step r G M j = (
    let ns = {i. i \<notin> Vs M \<and> {i,j} \<in> G} in
    if ns \<noteq> {} \<and> j \<notin> Vs M
    then let i = min_on_rel ns r in insert {i,j} M
    else M
  )"

lemma step_cases[case_names no_neighbor j_matched new_match]:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {} \<Longrightarrow> j \<notin> Vs M \<Longrightarrow> P"
  shows "P"
  using assms
  by blast

definition "ranking' r G M \<equiv> foldl (step r G) M"
abbreviation "ranking r G \<equiv> ranking' r G {}"

lemma ranking_Nil[simp]: "ranking' r G M [] = M"
  unfolding ranking'_def by simp

lemma ranking_Cons: "ranking' r G M (j#js) = ranking' r G (step r G M j) js"
  unfolding ranking'_def
  by simp

lemma finite_unmatched_neighbors[intro]:
  "finite (Vs G) \<Longrightarrow> finite {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  by (rule finite_subset[of _ "Vs G"]) auto

lemma step_subgraph:
  assumes "finite (Vs G)"
  assumes "M \<subseteq> G" 
  assumes "preorder_on' {i. {i,j} \<in> G} r" (is "preorder_on' ?N r")
  shows "step r G M j \<subseteq> G"
  using assms
proof (cases M j G rule: step_cases)
  case new_match
  let ?ns = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  let ?i = "min_on_rel ?ns r"

  from new_match assms have "?i \<in> ?ns"
    by (intro min_if_finite preorder_on'_subset[where S = ?N and T = ?ns]) auto

  with assms show ?thesis
    by (simp add: step_def)
qed (use assms in \<open>simp_all add: step_def\<close>)

lemma ranking'_subgraph:
  assumes "finite (Vs G)"
  assumes "M \<subseteq> G"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  shows "ranking' r G M js \<subseteq> G"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: step_subgraph)

locale wf_ranking_order =
  fixes L :: "'a set" and R :: "'a set"
  fixes G :: "'a graph"

  assumes finite_L: "finite L" and finite_R: "finite R"
  assumes bipartite_graph: "bipartite G L R"
  assumes parts_minimal: "Vs G = L \<union> R"
begin

sublocale graph_abs G
  using bipartite_graph finite_L finite_R
  by (intro finite_parts_bipartite_graph_abs)

lemmas finite_graph = finite_E

lemma finite_subsets: "finite {M. M \<subseteq> G}"
  using finite_graph by blast

lemma preorder_on_neighborsI:
  assumes "set js \<subseteq> R"
  assumes "r \<in> preorders_on L"
  assumes "j \<in> set js"
  shows "preorder_on' {i. {i,j} \<in> G} r"
proof -
  from \<open>r \<in> preorders_on L\<close> have preorder: "preorder_on' L r"
    by (auto dest: preorders_onD intro: preorder_on_imp_preorder_on')

  from assms bipartite_graph have "{i. {i,j} \<in> G} \<subseteq> L"
    by (auto dest: bipartite_edgeD)

  with preorder show ?thesis
    by (auto intro: preorder_on'_subset)
qed
end
end