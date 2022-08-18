theory Ranking_Order
  imports
    More_Graph
    "Treaps.Random_List_Permutation"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

declare vs_member_intro[rule del]

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

lemma step_cases'[case_names no_neighbor j_matched new_match]:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {} \<Longrightarrow> j \<notin> Vs M \<Longrightarrow> P"
  shows "P"
  using assms
  by blast

lemma finite_unmatched_neighbors[intro]:
  "finite (Vs G) \<Longrightarrow> finite {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  by (rule finite_subset[of _ "Vs G"]) (auto intro: vs_member_intro)

lemma step_cases[consumes 2, case_names no_neighbor j_matched new_match]:
  fixes G M j
  defines "ns \<equiv> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  assumes "preorder_on' {i. {i,j} \<in> G} r" "finite (Vs G)"
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes 
    "\<lbrakk>ns \<noteq> {}; j \<notin> Vs M; min_on_rel ns r \<in> ns; 
      \<not>(\<exists>i'\<in>ns. (i', min_on_rel ns r) \<in> r \<and> (min_on_rel ns r, i') \<notin> r)\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases M j G rule: step_cases')
  case new_match

  have "min_on_rel ns r \<in> ns"
  proof (intro min_if_finite, goal_cases)
    case 1
    from \<open>preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      unfolding ns_def
      by (auto intro: preorder_on'_subset)
  next
    case 2
    from \<open>finite (Vs G)\<close> show ?case
      unfolding ns_def
      by blast
  next
    case 3
    from new_match show ?case
      unfolding ns_def
      by blast
  qed

  have "\<not>(\<exists>i'\<in>ns. (i', min_on_rel ns r) \<in> r \<and> (min_on_rel ns r, i') \<notin> r)"
  proof (intro min_if_finite, goal_cases)
    case 1
    from \<open>preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      unfolding ns_def
      by (auto intro: preorder_on'_subset)
  next
    case 2
    from \<open>finite (Vs G)\<close> show ?case
      unfolding ns_def
      by blast
  next
    case 3
    from new_match show ?case
      unfolding ns_def
      by blast
  qed

  with new_match \<open>min_on_rel ns r \<in> ns\<close> assms show ?thesis
    by blast
qed (use assms in \<open>blast+\<close>)

definition "ranking' r G M \<equiv> foldl (step r G) M"
abbreviation "ranking r G \<equiv> ranking' r G {}"

lemma ranking_Nil[simp]: "ranking' r G M [] = M"
  unfolding ranking'_def by simp

lemma ranking_Cons: "ranking' r G M (j#js) = ranking' r G (step r G M j) js"
  unfolding ranking'_def
  by simp

lemma ranking_append: "ranking' r G M (js@js') = ranking' r G (ranking' r G M js) js'"
  unfolding ranking'_def
  by simp


lemma step_subgraph:
  assumes fin: "finite (Vs G)"
  assumes preorder: "preorder_on' {i. {i,j} \<in> G} r" (is "preorder_on' ?N r")
  assumes "M \<subseteq> G" 
  shows "step r G M j \<subseteq> G"
  using preorder fin
  by (cases rule: step_cases[where M = M]) (use assms in \<open>simp_all add: step_def\<close>)

lemma ranking_subgraph:
  assumes "finite (Vs G)"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  assumes "M \<subseteq> G"
  shows "ranking' r G M js \<subseteq> G"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: step_subgraph)

lemma matching_step:
  assumes fin: "finite (Vs G)"
  assumes preorder: "preorder_on' {i. {i,j} \<in> G} r"
  assumes "matching M"
  shows "matching (step r G M j)"
  using preorder fin
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro: matching_insert\<close>)

lemma matching_ranking:
  assumes "finite (Vs G)"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  assumes "matching M"
  shows "matching (ranking' r G M js)"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: matching_step)

lemma step_mono:
  assumes "e \<in> M"
  shows "e \<in> step r G M j"
  using assms
  by (cases M j G rule: step_cases')
     (auto simp: step_def)

lemma ranking_mono:
  assumes "e \<in> M"
  shows "e \<in> ranking' r G M js"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: step_mono)

lemma ranking_mono_vs:
  assumes "v \<in> Vs M"
  shows "v \<in> Vs (ranking' r G M js)"
  using assms
  by (meson ranking_mono vs_member)

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
lemmas finite_vs = graph[THEN conjunct2]

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

lemma neighbors_right_subset_left: "j \<in> R \<Longrightarrow> {i. {i,j} \<in> G} \<subseteq> L"
  using bipartite_graph
  by (auto dest: bipartite_edgeD)

lemma finite_neighbors:
  "finite {i. {i,j} \<in> G}"
  by (rule finite_subset[of _ "Vs G"])
     (auto simp: graph intro: vs_member_intro)

lemma finite_unmatched_neighbors:
  "finite {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  by (rule finite_subset[of _ "Vs G"])
     (auto simp: graph intro: vs_member_intro)

lemma unmatched_neighbors_L:
  assumes "j \<in> R"
  shows "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<subseteq> L"
  using assms bipartite_graph
  by (auto dest: bipartite_edgeD)

lemma min_in_L:
  assumes "preorder_on' {i. {i,j} \<in> G} r"
  assumes "j \<in> R"
  assumes "i \<notin> Vs M" "{i,j} \<in> G"
  shows "min_on_rel {i. i \<notin> Vs M \<and> {i, j} \<in> G} r \<in> L" (is "min_on_rel ?S r \<in> L")
proof -
  from assms have "min_on_rel ?S r \<in> ?S"
    by (intro min_if_finite finite_unmatched_neighbors)
       (auto intro: preorder_on'_subset)

  with \<open>j \<in> R\<close> bipartite_graph show ?thesis
    by (auto dest: bipartite_edgeD)
qed

lemma unmatched_R_in_step_if:
  assumes preorder: "preorder_on' {i. {i,j'} \<in> G} r"
  assumes "j' \<in> R" "j' \<noteq> j"
  assumes "j \<notin> L" "j \<notin> Vs M"
  shows "j \<notin> Vs (step r G M j')"
  using assms
  by (cases M j' G rule: step_cases')
     (auto simp: step_def vs_insert dest: min_in_L)

lemma unmatched_R_in_ranking_if:
  assumes "preorder_on L r"
  assumes "set js \<subseteq> R"
  assumes "j \<notin> L" "j \<notin> set js"
  assumes "j \<notin> Vs M"
  shows "j \<notin> Vs (ranking' r G M js)"
  using assms
proof (induction js arbitrary: M)
  case (Cons j' js)

  then have "j \<notin> Vs (step r G M j')"
    by (intro unmatched_R_in_step_if preorder_on_neighborsI[where js = "j'#js"] preorders_onI)
       auto

  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma bipartite_step:
  assumes preorder: "preorder_on' {i. {i,j} \<in> G} r"
  assumes "bipartite M L R"
  assumes "j \<in> R"
  shows "bipartite (step r G M j) L R"
  using preorder finite_vs
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro: bipartite_insertI dest: neighbors_right_subset_left\<close>)

lemma bipartite_ranking:
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  assumes "set js \<subseteq> R"
  assumes "bipartite M L R"
  shows "bipartite (ranking' r G M js) L R"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: bipartite_step)

lemma ranking_subgraph:
  assumes "r \<in> preorders_on L"
  assumes "set js \<subseteq> R"
  shows "ranking r G js \<subseteq> G"
  using assms graph
  by (intro ranking_subgraph)
     (auto intro: preorder_on_neighborsI ranking_subgraph)

lemma the_ranking_match_left:
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> G} r"
  assumes "matching M"
  assumes "bipartite M L R"
  assumes j_matched: "j \<in> Vs (ranking' r G M js)"
  assumes "j \<in> R"
  assumes "set js \<subseteq> R"
  shows "(THE i. {i,j} \<in> ranking' r G M js) \<in> L"
proof -
  from j_matched obtain e where e: "e \<in> ranking' r G M js" "j \<in> e"
    by (auto elim: vs_member_elim)

  from assms have bipartite: "bipartite (ranking' r G M js) L R"
    by (auto intro: bipartite_ranking)

  with e obtain u v where uv: "e = {u,v}" "u \<noteq> v" "u \<in> L" "v \<in> R"
    by (auto elim: bipartite_edgeE)

  with bipartite \<open>j \<in> R\<close> e have "v = j"
    by (auto intro: bipartite_eqI)

  with e uv finite_vs assms have "(THE i. {i,j} \<in> ranking' r G M js) = u"
    by (intro the_match matching_ranking)
       auto

  with \<open>u \<in> L\<close> show ?thesis
    by blast
qed

end
end