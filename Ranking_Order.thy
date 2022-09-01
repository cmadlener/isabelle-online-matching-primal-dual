theory Ranking_Order
  imports
    More_Graph
    "Treaps.Random_List_Permutation"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

declare vs_member_intro[rule del]

lemma split_list_distinct:
  assumes "distinct xs"
  assumes "x \<in> set xs"
  shows "\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set ys \<and> x \<notin> set zs"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  show ?case
  proof cases
    assume "x = a"
    with Cons show ?case
      by fastforce
  next
    assume "x \<noteq> a"
    with Cons show ?case
      by (fastforce intro!: Cons_eq_appendI)
  qed
qed

text \<open>Weaker versions of \<^term>\<open>refl_on\<close> (and \<^term>\<open>preorder_on\<close>/\<^term>\<open>linorder_on\<close>) that don't enforce
that the relation is only defined on the given set. Alternative would be to weaken all lemmas
by using stronger assumptions.\<close>
definition "refl_on' S r \<longleftrightarrow> (\<forall>x\<in>S. (x,x) \<in> r)"
definition "preorder_on' S r \<longleftrightarrow> refl_on' S r \<and> trans r"
definition "linorder_on' S r \<longleftrightarrow> refl_on' S r \<and> antisym r \<and> trans r \<and> total_on S r"

definition "preorders_on S \<equiv> {r. preorder_on S r}"

definition "total_preorder_on S r \<longleftrightarrow> preorder_on S r \<and> total_on S r"
definition "total_preorder_on' S r \<longleftrightarrow> preorder_on' S r \<and> total_on S r"

definition "total_preorders_on S \<equiv> {r. total_preorder_on S r}"

lemma refl_on'D: "refl_on' S r \<Longrightarrow> a \<in> S \<Longrightarrow> (a,a) \<in> r"
  unfolding refl_on'_def
  by blast

lemma refl_on'_Restr: "refl_on' S r \<Longrightarrow> refl_on' S (Restr r S)"
  unfolding refl_on'_def
  by blast

lemma linorder_on'_refl_on'D: "linorder_on' S r \<Longrightarrow> refl_on' S r"
  unfolding linorder_on'_def
  by blast

lemma linorder_on'_transD: "linorder_on' S r \<Longrightarrow> trans r"
  unfolding linorder_on'_def
  by blast

lemma linorder_on'_antisymD: "linorder_on' S r \<Longrightarrow> antisym r"
  unfolding linorder_on'_def
  by blast

lemma preorders_onD: "r \<in> preorders_on S \<Longrightarrow> preorder_on S r"
  unfolding preorders_on_def
  by blast

lemma preorders_onI[intro]: "preorder_on S r \<Longrightarrow> r \<in> preorders_on S"
  unfolding preorders_on_def
  by blast

lemma total_preorders_onD: "r \<in> total_preorders_on S \<Longrightarrow> total_preorder_on S r"
  unfolding total_preorders_on_def
  by blast

lemma total_preorders_onI[intro]: "total_preorder_on S r \<Longrightarrow> r \<in> total_preorders_on S"
  unfolding total_preorders_on_def
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

lemma finite_total_preorders_on[intro]:
  assumes "finite S"
  shows "finite (total_preorders_on S)"
  using assms
  by (auto intro!: finite_subset[OF _ finite_preorders_on] dest!: total_preorders_onD simp: total_preorder_on_def)

lemma refl_on_imp_refl_on': "refl_on S r \<Longrightarrow> refl_on' S r"
  unfolding refl_on_def refl_on'_def
  by blast

lemma linorder_on_imp_linorder_on': "linorder_on S r \<Longrightarrow> linorder_on' S r"
  unfolding linorder_on_def linorder_on'_def
  by (auto dest: refl_on_imp_refl_on')

lemma linorder_on_imp_preorder_on: "linorder_on S r \<Longrightarrow> preorder_on S r"
  unfolding linorder_on_def preorder_on_def
  by blast

lemma linorder_on'_imp_preorder_on': "linorder_on' S r \<Longrightarrow> preorder_on' S r"
  unfolding linorder_on'_def preorder_on'_def
  by blast

lemma preorder_on_imp_preorder_on': "preorder_on S r \<Longrightarrow> preorder_on' S r"
  unfolding preorder_on_def preorder_on'_def
  by (blast intro: refl_on_imp_refl_on')

lemma total_preorder_on_imp_total_preorder_on': "total_preorder_on S r \<Longrightarrow> total_preorder_on' S r"
  unfolding total_preorder_on_def total_preorder_on'_def
  by (auto intro: preorder_on_imp_preorder_on')

lemma total_preorder_on'_imp_preorder_on': "total_preorder_on' S r \<Longrightarrow> preorder_on' S r"
  unfolding total_preorder_on'_def by blast

lemma preorder_on'_transD: "preorder_on' S r \<Longrightarrow> trans r"
  unfolding preorder_on'_def
  by blast

lemma preorder_on'_refl_on'D: "preorder_on' S r \<Longrightarrow> refl_on' S r"
  unfolding preorder_on'_def
  by blast

lemma refl_on'_subset:
  "refl_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> refl_on' T r"
  unfolding refl_on'_def
  by blast

lemma linorder_on'_subset:
  "linorder_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> linorder_on' T r"
  unfolding linorder_on'_def
  by (auto intro: refl_on'_subset total_on_subset)

lemma preorder_on'_subset:
  "preorder_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> preorder_on' T r"
  unfolding preorder_on'_def
  by (auto intro: refl_on'_subset total_on_subset)

lemma total_preorder_on'_subset:
  "total_preorder_on' S r \<Longrightarrow> T \<subseteq> S \<Longrightarrow> total_preorder_on' T r"
  unfolding total_preorder_on'_def
  by (auto intro: preorder_on'_subset total_on_subset)

lemma total_on_Restr:
  "total_on S r \<Longrightarrow> total_on S (Restr r S)"
  unfolding total_on_def
  by blast

lemma linorder_on'_Restr:
  "linorder_on' S r \<Longrightarrow> linorder_on' S (Restr r S)"
  unfolding linorder_on'_def
  by (auto intro: refl_on'_Restr antisym_subset trans_Restr total_on_Restr)
  
definition determ_is_min_rel :: "('a::linorder \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" where
  "determ_is_min_rel P r x = (P x \<and> (\<forall>y. (P y \<longrightarrow> (x,y) \<in> r) \<and> ((P y \<and> x \<noteq> y \<and> (y,x) \<in> r) \<longrightarrow> x < y)))"

definition determ_min_rel :: "('a::linorder \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> 'a" where
  "determ_min_rel P r = (THE x. determ_is_min_rel P r x)"

definition determ_min_on_rel :: "'a::linorder set \<Rightarrow> 'a rel \<Rightarrow> 'a" where
  "determ_min_on_rel S r = determ_min_rel (\<lambda>x. x \<in> S) r"

lemma ex1_min_if_finite:
  fixes S :: "('a :: linorder) set"
  shows "\<lbrakk> finite S; S \<noteq> {}; total_preorder_on' S r \<rbrakk> \<Longrightarrow> \<exists>!m\<in>S. (\<forall>x\<in>S. (m,x) \<in> r \<and> (m \<noteq> x \<and> (x,m) \<in> r \<longrightarrow> m < x))"
proof (induction rule: finite.induct)
  case (insertI A a)
  then show ?case
  proof (cases "A \<noteq> {}")
    case True
    from insertI have "total_preorder_on' A r"
      by (auto intro: total_preorder_on'_subset)

    with True insertI obtain m where m: "m\<in>A" "\<forall>x\<in>A. (m,x) \<in> r \<and> (m \<noteq> x \<and> (x,m) \<in> r \<longrightarrow> m < x)"
      by auto

    from \<open>total_preorder_on' (insert a A) r\<close> show ?thesis
    proof (intro ex_ex1I, goal_cases)
      case 1
      with m show ?case
        unfolding total_preorder_on'_def preorder_on'_def
        by (smt (verit, del_insts) insertCI insertE not_less_iff_gr_or_eq order_less_trans refl_on'_def total_on_def transD)
    next
      case (2 m m')
      then show ?case
        by (metis not_less_iff_gr_or_eq)
    qed
  next
    case False

    with \<open>total_preorder_on' (insert a A) r\<close> show ?thesis
      by (intro ex1I[of _ a])
         (auto simp: total_preorder_on'_def preorder_on'_def intro: refl_on'D)
  qed
qed simp

lemma ex1_is_min_if_finite:
  fixes S :: "('a::linorder) set"
  assumes "total_preorder_on' S r"
  assumes "finite S" "S \<noteq> {}"
  shows "\<exists>!x. determ_is_min_rel (\<lambda>x. x \<in> S) r x"
  using assms ex1_min_if_finite
  unfolding determ_is_min_rel_def
  by (smt (verit))

lemma min_if_finite:
  fixes S :: "('a::linorder) set"
  assumes "total_preorder_on' S r"
  assumes "finite S" "S \<noteq> {}"
  shows "determ_min_on_rel S r \<in> S" 
    and "\<forall>x\<in>S. (determ_min_on_rel S r, x) \<in> r \<and> 
      (determ_min_on_rel S r \<noteq> x \<and> (x, determ_min_on_rel S r) \<in> r \<longrightarrow> determ_min_on_rel S r < x)"
  using assms ex1_is_min_if_finite
  unfolding determ_min_on_rel_def determ_min_rel_def determ_is_min_rel_def
  by (smt (verit, ccfv_threshold) the_equality)+

lemma min_rel_linorder_eq:
  assumes "linorder_on' {x. P x} r"
  assumes "P a"
  assumes "\<forall>y. P y \<longrightarrow> (a,y) \<in> r"
  shows "determ_min_rel P r = a"
  using assms
  unfolding determ_min_rel_def determ_is_min_rel_def
  by (auto simp add: antisym_def linorder_on'_def)

lemma min_on_rel_linorder_eq:
  assumes "linorder_on' S r"
  assumes "a \<in> S"
  assumes "\<forall>y\<in>S. (a,y) \<in> r"
  shows "determ_min_on_rel S r = a"
  using assms
  unfolding determ_min_on_rel_def
  by (auto intro!: min_rel_linorder_eq)

lemma min_rel_eq:
  assumes "P a"
  assumes "\<forall>y. P y \<longrightarrow> (a,y) \<in> r"
  assumes "\<forall>y. (P y \<and> a \<noteq> y \<and> (y,a) \<in> r) \<longrightarrow> a < y"
  shows "determ_min_rel P r = a"
  using assms
  unfolding determ_min_rel_def determ_is_min_rel_def
  by (smt (verit, ccfv_threshold) not_less_iff_gr_or_eq the_equality)

lemma min_on_rel_eq:
  assumes "a \<in> S"
  assumes "\<forall>y\<in>S. (a,y) \<in> r"
  assumes "\<forall>y\<in>S. (a \<noteq> y \<and> (y,a) \<in> r) \<longrightarrow> a < y"
  shows "determ_min_on_rel S r = a"
  using assms
  unfolding determ_min_on_rel_def
  by (auto intro: min_rel_eq)

lemma min_on_rel_singleton:
  assumes "refl_on' {a} r"
  shows "determ_min_on_rel {a} r = a"
  using assms
  by (auto simp: refl_on'_def determ_min_on_rel_def determ_min_rel_def determ_is_min_rel_def)

lemma min_on_rel_least:
  assumes "total_preorder_on' S r"
  assumes S: "finite S" "S \<noteq> {}"
  assumes "y \<in> S"
  shows "(determ_min_on_rel S r, y) \<in> r"
  using assms
  by (simp add: min_if_finite)


definition step :: "('a::linorder \<times> 'a) set \<Rightarrow> 'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a graph" where
  "step r G M j = (
    let ns = {i. i \<notin> Vs M \<and> {i,j} \<in> G} in
    if ns \<noteq> {} \<and> j \<notin> Vs M
    then let i = determ_min_on_rel ns r in insert {i,j} M
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
  fixes G M and j :: "'a::linorder"
  defines "ns \<equiv> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  assumes "total_preorder_on' {i. {i,j} \<in> G} r" "finite (Vs G)"
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes 
    "\<lbrakk>ns \<noteq> {}; j \<notin> Vs M; determ_min_on_rel ns r \<in> ns; 
      (\<forall>i'\<in>ns. (determ_min_on_rel ns r, i') \<in> r \<and> (determ_min_on_rel ns r \<noteq> i' \<and> (i', determ_min_on_rel ns r) \<in> r \<longrightarrow> determ_min_on_rel ns r < i'))\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof (cases M j G rule: step_cases')
  case new_match

  have "determ_min_on_rel ns r \<in> ns"
  proof (intro min_if_finite, goal_cases)
    case 1
    from \<open>total_preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      unfolding ns_def
      by (auto intro: total_preorder_on'_subset)
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

  have "(\<forall>i'\<in>ns. (determ_min_on_rel ns r, i') \<in> r \<and> (determ_min_on_rel ns r \<noteq> i' \<and> (i', determ_min_on_rel ns r) \<in> r \<longrightarrow> determ_min_on_rel ns r < i'))"
  proof (intro min_if_finite, goal_cases)
    case 1
    from \<open>total_preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      unfolding ns_def
      by (auto intro: total_preorder_on'_subset)
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

  with new_match \<open>determ_min_on_rel ns r \<in> ns\<close> assms show ?thesis
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

lemma step_insertI:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {}" "j \<notin> Vs M"
  assumes "i = determ_min_on_rel {i. i \<notin> Vs M \<and> {i,j} \<in> G} r"
  shows "step r G M j = insert {i,j} M"
  using assms
  by (simp add: step_def)

lemma step_subgraph:
  assumes fin: "finite (Vs G)"
  assumes preorder: "total_preorder_on' {i. {i,j} \<in> G} r"
  assumes "M \<subseteq> G" 
  shows "step r G M j \<subseteq> G"
  using preorder fin
  by (cases rule: step_cases[where M = M]) (use assms in \<open>simp_all add: step_def\<close>)

lemma ranking_subgraph:
  assumes "finite (Vs G)"
  assumes "\<forall>j\<in>set js. total_preorder_on' {i. {i,j} \<in> G} r"
  assumes "M \<subseteq> G"
  shows "ranking' r G M js \<subseteq> G"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: step_subgraph)

lemma matching_step:
  assumes fin: "finite (Vs G)"
  assumes preorder: "total_preorder_on' {i. {i,j} \<in> G} r"
  assumes "matching M"
  shows "matching (step r G M j)"
  using preorder fin
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro: matching_insert\<close>)

lemma matching_ranking:
  assumes "finite (Vs G)"
  assumes "\<forall>j\<in>set js. total_preorder_on' {i. {i,j} \<in> G} r"
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

lemma edge_in_step:
  assumes "e \<in> step r G M j"
  shows "e \<in> M \<or> j \<in> e"
  using assms
  by (auto simp: step_def split: if_splits)

lemma edge_in_ranking:
  assumes "e \<in> ranking' r G M js"
  shows "e \<in> M \<or> (\<exists>j \<in> set js. j \<in> e)"
  using assms
  by (induction js arbitrary: M)
     (auto dest: edge_in_step simp: ranking_Cons)

lemma edge_in_rankingE:
  assumes "e \<in> ranking' r G M js"
  obtains "e \<in> M" | j where "j \<in> set js" "j \<in> e"
  using assms
  by (auto dest: edge_in_ranking)

lemma step_matches_if_possible:
  assumes "j \<notin> Vs M"
  assumes "{i,j} \<in> G"
  assumes "i \<notin> Vs M"
  shows "j \<in> Vs (step r G M j)"
  using assms
  by (cases M j G rule: step_cases')
     (auto simp: step_def vs_insert)

locale wf_ranking_order =
  fixes L :: "('a::linorder) set" and R :: "'a set"
  fixes G :: "'a graph"

  assumes finite_L: "finite L" and finite_R: "finite R"
  assumes bipartite_graph: "bipartite G L R"
  assumes parts_minimal: "Vs G = L \<union> R"
begin

sublocale graph_abs G
  using bipartite_graph finite_L finite_R
  by (intro finite_parts_bipartite_graph_abs)

lemmas finite_graph[intro,simp] = finite_E
lemmas finite_vs[intro] = graph[THEN conjunct2]

lemma parts_disjoint[intro,simp]: "L \<inter> R = {}"
  using bipartite_graph
  by (auto dest: bipartite_disjointD)

lemma bipartite_FalseD[dest]:  "x \<in> L \<Longrightarrow> x \<in> R \<Longrightarrow> False"
  using bipartite_graph
  by (auto dest: bipartite_disjointD)


lemma finite_vs_subgraph: "H \<subseteq> G \<Longrightarrow> finite (Vs H)"
  using finite_vs
  by (auto intro: finite_subset dest: Vs_subset)

lemma finite_subsets: "finite {M. M \<subseteq> G}"
  using finite_graph by blast

lemma neighbors_right_subset_left: "H \<subseteq> G \<Longrightarrow> j \<in> R \<Longrightarrow> {i. {i,j} \<in> H} \<subseteq> L"
  using bipartite_graph
  by (auto dest: bipartite_edgeD)

lemma neighbors_right_subset_left_remove_vertices: "j \<in> R \<Longrightarrow> {i. {i,j} \<in> G \<setminus> X} \<subseteq> L - X"
  by (auto dest: neighbors_right_subset_left[OF remove_vertices_subgraph] edges_are_Vs intro: remove_vertices_not_vs')

lemma preorder_on_neighborsI[intro]:
  assumes "H \<subseteq> G"
  assumes "total_preorder_on L r"
  assumes "j \<in> R"
  shows "total_preorder_on' {i. {i,j} \<in> H} r"
  using assms
  by (auto dest: total_preorder_on_imp_total_preorder_on' neighbors_right_subset_left intro: total_preorder_on'_subset)

lemma preorder_on_neighborsI_remove_vertices[intro]:
  assumes "total_preorder_on (L - X) r"
  assumes "j \<in> R"
  shows "total_preorder_on' {i. {i,j} \<in> G \<setminus> X} r"
  using assms
  by (auto dest: total_preorder_on_imp_total_preorder_on' neighbors_right_subset_left_remove_vertices intro: total_preorder_on'_subset)

lemma linorder_on_neighborsI[intro]:
  assumes "H \<subseteq> G"
  assumes "linorder_on L r"
  assumes "j \<in> R"
  shows "linorder_on' {i. {i,j} \<in> H} r"
  using assms
  by (auto dest: linorder_on_imp_linorder_on' neighbors_right_subset_left intro: linorder_on'_subset)

lemma linorder_on_neighborsI_remove_vertices[intro]:
  assumes "linorder_on (L - X) r"
  assumes "j \<in> R"
  shows "linorder_on' {i. {i,j} \<in> G \<setminus> X} r"
  using assms
  by (auto dest: linorder_on_imp_linorder_on' neighbors_right_subset_left_remove_vertices intro: linorder_on'_subset)

lemma finite_neighbors:
  "H \<subseteq> G \<Longrightarrow> finite {i. {i,j} \<in> H}"
  by (rule finite_subset[of _ "Vs G"])
     (auto simp: graph intro: vs_member_intro)

lemma finite_unmatched_neighbors:
  "H \<subseteq> G \<Longrightarrow> finite {i. i \<notin> Vs M \<and> {i,j} \<in> H}"
  by (rule finite_subset[of _ "Vs G"])
     (auto simp: graph intro: vs_member_intro)

lemma unmatched_neighbors_L:
  assumes "H \<subseteq> G"
  assumes "j \<in> R"
  shows "{i. i \<notin> Vs M \<and> {i,j} \<in> H} \<subseteq> L"
  using assms bipartite_graph
  by (auto dest: bipartite_edgeD)

lemma min_in_L:
  assumes "H \<subseteq> G"
  assumes "total_preorder_on' {i. {i,j} \<in> H} r"
  assumes "j \<in> R"
  assumes "i \<notin> Vs M" "{i,j} \<in> H"
  shows "determ_min_on_rel {i. i \<notin> Vs M \<and> {i, j} \<in> H} r \<in> L" (is "determ_min_on_rel ?S r \<in> L")
proof -
  from assms have "determ_min_on_rel ?S r \<in> ?S"
    by (intro min_if_finite finite_unmatched_neighbors)
       (auto intro: total_preorder_on'_subset)

  with \<open>H \<subseteq> G\<close> \<open>j \<in> R\<close> bipartite_graph show ?thesis
    by (auto dest: bipartite_edgeD bipartite_subgraph)
qed

lemma unmatched_R_in_step_if:
  assumes "H \<subseteq> G"
  assumes preorder: "total_preorder_on' {i. {i,j'} \<in> H} r"
  assumes "j' \<in> R" "j' \<noteq> j"
  assumes "j \<notin> L" "j \<notin> Vs M"
  shows "j \<notin> Vs (step r H M j')"
  using assms
  by (cases M j' H rule: step_cases')
     (auto simp: step_def vs_insert dest: min_in_L)

lemma unmatched_R_in_ranking_if:
  assumes "H \<subseteq> G"
  assumes "\<forall>j \<in> set js. total_preorder_on' {i. {i,j} \<in> H} r"
  assumes "set js \<subseteq> R"
  assumes "j \<notin> L" "j \<notin> set js"
  assumes "j \<notin> Vs M"
  shows "j \<notin> Vs (ranking' r H M js)"
  using assms
proof (induction js arbitrary: M)
  case (Cons j' js)

  then have "j \<notin> Vs (step r H M j')"
    by (intro unmatched_R_in_step_if) auto

  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma bipartite_step:
  assumes subgraph: "H \<subseteq> G"
  assumes preorder: "total_preorder_on' {i. {i,j} \<in> H} r"
  assumes "bipartite M L R"
  assumes "j \<in> R"
  shows "bipartite (step r H M j) L R"
  using preorder finite_vs_subgraph[OF subgraph]
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro!: bipartite_insertI dest: neighbors_right_subset_left\<close>)

lemma bipartite_ranking:
  assumes "H \<subseteq> G"
  assumes "\<forall>j\<in>set js. total_preorder_on' {i. {i,j} \<in> H} r"
  assumes "set js \<subseteq> R"
  assumes "bipartite M L R"
  shows "bipartite (ranking' r H M js) L R"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: bipartite_step)

lemma ranking_subgraph:
  assumes "H \<subseteq> G"
  assumes "total_preorder_on L r"
  assumes "set js \<subseteq> R"
  shows "ranking r H js \<subseteq> H"
  using assms graph
  by (intro ranking_subgraph)
     (auto intro: ranking_subgraph finite_vs_subgraph)

lemma ranking_subgraph':
  assumes "H \<subseteq> G"
  assumes "total_preorder_on L r"
  assumes "set js \<subseteq> R"
  shows "e \<in> ranking r H js \<Longrightarrow> e \<in> H"
  using assms
  by (auto dest: ranking_subgraph)

lemma ranking_match_neighbor_L:
  assumes "H \<subseteq> G"
  assumes "total_preorder_on L r"
  assumes "set js \<subseteq> R"
  assumes "j \<in> R"
  assumes "{i,j} \<in> ranking r H js"
  shows "i \<in> L"
  using assms bipartite_graph
  by (auto dest: ranking_subgraph' bipartite_edgeD)

lemma the_ranking_match_left:
  assumes "H \<subseteq> G"
  assumes "\<forall>j\<in>set js. total_preorder_on' {i. {i,j} \<in> H} r"
  assumes "matching M"
  assumes "bipartite M L R"
  assumes j_matched: "j \<in> Vs (ranking' r H M js)"
  assumes "j \<in> R"
  assumes "set js \<subseteq> R"
  shows "{THE i. {i,j} \<in> ranking' r H M js, j} \<in> ranking' r H M js"
    "(THE i. {i,j} \<in> ranking' r H M js) \<in> L"
proof -
  from j_matched obtain e where e: "e \<in> ranking' r H M js" "j \<in> e"
    by (auto elim: vs_member_elim)

  from assms have bipartite: "bipartite (ranking' r H M js) L R"
    by (auto intro: bipartite_ranking)

  with e obtain u v where uv: "e = {u,v}" "u \<noteq> v" "u \<in> L" "v \<in> R"
    by (auto elim: bipartite_edgeE)

  with bipartite \<open>j \<in> R\<close> e have "v = j"
    by (auto intro: bipartite_eqI)

  with e uv assms have "(THE i. {i,j} \<in> ranking' r H M js) = u"
    by (intro the_match matching_ranking finite_subset[OF Vs_subset finite_vs])
        auto  

  with e uv \<open>v = j\<close> show "{THE i. {i, j} \<in> ranking' r H M js, j} \<in> ranking' r H M js"
    "(THE i. {i, j} \<in> ranking' r H M js) \<in> L"
    by auto
qed

lemma step_remove_unmatched_eq:
  assumes preorder: "total_preorder_on L r"

  assumes "i \<in> L" "j \<in> R"
  assumes "i \<notin> Vs (step r G M j)"
  shows "step r (G \<setminus> {i}) M j = step r G M j"
proof -
  from preorder \<open>j \<in> R\<close> have "total_preorder_on' {i. {i,j} \<in> G} r"
    by auto

  from this finite_vs
  show ?thesis
  proof (cases rule: step_cases[where M = M])
    case new_match
    let ?ns = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G}"
    and ?ns' = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G \<setminus> {i}}"

    let ?min = "determ_min_on_rel ?ns r"
    and ?min' = "determ_min_on_rel ?ns' r"

    from \<open>j \<in> R\<close> have "?ns \<subseteq> L" "?ns' \<subseteq> ?ns"
      by (auto dest: remove_vertices_subgraph' neighbors_right_subset_left[OF subset_refl])

    then have "?ns' \<subseteq> L"
      by blast

    from new_match have step_eq: "step r G M j = insert {?min, j} M"
      by (simp add: step_def)

    with \<open>i \<notin> Vs (step r G M j)\<close> have "?min \<noteq> i" "j \<noteq> i"
      by (auto simp: vs_insert)

    with \<open>?min \<in> ?ns\<close> have "?ns' \<noteq> {}"
      by (auto intro: in_remove_verticesI)

    have "?min' = ?min"
    proof (intro min_on_rel_eq, goal_cases)
      case 1
      from \<open>?min \<in> ?ns\<close> \<open>?min \<noteq> i\<close> \<open>j \<noteq> i\<close> show ?case
        by (auto intro: in_remove_verticesI)
    next
      case 2
      from \<open>?ns' \<subseteq> ?ns\<close> new_match show ?case
        by blast
    next
      case 3
      from \<open>?ns' \<subseteq> ?ns\<close> new_match show ?case
        by blast
    qed

    with \<open>j \<notin> Vs M\<close> \<open>?ns' \<noteq> {}\<close> show ?thesis
      by (subst step_eq) (simp add: step_def)
  qed (use assms in \<open>auto simp: step_def dest: remove_vertices_subgraph'\<close>)
qed

lemma ranking_remove_unmatched_eq:
  assumes preorder: "total_preorder_on L r"

  assumes "i \<in> L" "set js \<subseteq> R"
  assumes "i \<notin> Vs (ranking' r G M js)"
  shows "ranking' r (G \<setminus> {i}) M js = ranking' r G M js"
  using assms
proof (induction js arbitrary: M)
  case (Cons j js)

  from Cons.prems have "step r (G \<setminus> {i}) M j = step r G M j"
    by (intro step_remove_unmatched_eq)
       (auto simp: ranking_Cons dest: ranking_mono_vs)

  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma dominance_order_matched:
  assumes preorder: "total_preorder_on L r"

  assumes "i \<in> L" "j \<in> R"
  assumes "set js = R"
  assumes "{i,j} \<in> G"

  assumes "{i',j} \<in> ranking r (G \<setminus> {i}) js"
  assumes less: "(i,i') \<in> r" "(i',i) \<notin> r"
  shows "i \<in> Vs (ranking r G js)"
proof -
  from \<open>set js = R\<close> \<open>j \<in> R\<close> obtain pre suff where js_split: "js = pre @ j # suff" "j \<notin> set pre"
    by (auto dest: split_list_first)

  with preorder \<open>set js = R\<close> \<open>j \<in> R\<close>
  have j_unmatched_pre: "j \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> j \<notin> Vs (ranking r G pre)"
    by (intro unmatched_R_in_ranking_if conjI)
       (auto dest: remove_vertices_subgraph')

  from preorder \<open>set js = R\<close> have preorder_neighbors:
    "j' \<in> set js \<Longrightarrow> total_preorder_on' {i'. {i', j'} \<in> G \<setminus> {i}} r" for j'
    by (auto dest: remove_vertices_subgraph')

  with \<open>set js = R\<close> preorder have bipartite_js: "bipartite (ranking r (G \<setminus> {i}) js) L R"
    by (intro bipartite_ranking)
       (auto dest: remove_vertices_subgraph')

  with \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close> \<open>j \<in> R\<close> have \<open>i' \<in> L\<close>
    by (auto dest: bipartite_edgeD)

  have "bipartite (ranking r (G \<setminus> {i}) pre) L R"
    by (intro bipartite_subgraph[OF bipartite_js])
       (auto simp: js_split ranking_append intro: ranking_mono)

  from preorder_neighbors have "matching (ranking r (G \<setminus> {i}) js)"
    by (auto intro!: matching_ranking)

  from \<open>i \<in> L\<close> \<open>i' \<in> L\<close> \<open>j \<in> R\<close> have "i \<noteq> j" "i' \<noteq> j"
    by auto

  from less have "i \<noteq> i'"
    by auto

  from preorder \<open>set js = R\<close> have "{i',j} \<in> G \<setminus> {i}"
    by (auto dest: remove_vertices_subgraph' 
             intro!: ranking_subgraph'[OF _ _ _ \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close>])

  show ?thesis
  proof (cases "i \<in> Vs (ranking r G pre)")
    case True
    with js_split show ?thesis
      by (auto simp: ranking_append dest: ranking_mono_vs)
  next
    case False

    have i'_unmatched_pre: "i' \<notin> Vs (ranking r (G \<setminus> {i}) pre)"
    proof (rule ccontr, simp)
      assume "i' \<in> Vs (ranking r (G \<setminus> {i}) pre)"
      then obtain e where e: "e \<in> ranking r (G \<setminus> {i}) pre" "i' \<in> e"
        by (auto elim: vs_member_elim)

      from e js_split have "e \<in> ranking r (G \<setminus> {i}) js"
        by (auto simp: ranking_append intro: ranking_mono)

      from e obtain j' where "j' \<in> e" "j' \<in> set pre"
        by (auto elim: edge_in_rankingE)

      with js_split \<open>set js = R\<close> have "j' \<in> R" "j' \<noteq> j"
        by auto

      with \<open>i' \<in> L\<close> \<open>j \<in> R\<close> \<open>i' \<in> e\<close> \<open>j' \<in> e\<close> have "e \<noteq> {i',j}" "e \<inter> {i',j} \<noteq> {}"
        by auto

      with \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close> \<open>e \<in> ranking r (G \<setminus> {i}) js\<close>
      have "\<not>matching (ranking r (G \<setminus> {i}) js)"
        unfolding matching_def
        by force

      with \<open>matching (ranking r (G \<setminus> {i}) js)\<close> show False
        by blast
    qed

    from assms False js_split have ranking_pre_eq: "ranking r (G \<setminus> {i}) pre = ranking r G pre"
      by (intro ranking_remove_unmatched_eq) auto

    let ?ns = "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G}"
    and ?ns' = "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}" 

    from False \<open>i \<noteq> j\<close> \<open>{i,j} \<in> G\<close> have *: "?ns = insert i ?ns'"
      by (auto intro: in_remove_vertices_vsI in_remove_verticesI 
               dest: edges_are_Vs remove_vertices_subgraph'
               simp: ranking_pre_eq)


    from i'_unmatched_pre \<open>{i',j} \<in> G \<setminus> {i}\<close> have "i' \<in> ?ns'"
      by auto

    have **: "determ_min_on_rel ?ns' r = i'"
    proof (rule ccontr)
      assume "determ_min_on_rel ?ns' r \<noteq> i'"
      then obtain i'' where i'': "i'' = determ_min_on_rel ?ns' r" "i'' \<noteq> i'"
        by blast   

      with \<open>i' \<in> ?ns'\<close> j_unmatched_pre have "step r (G \<setminus> {i}) (ranking r (G \<setminus> {i}) pre) j = insert {i'',j} (ranking r (G \<setminus> {i}) pre)"
        by (auto simp: step_def)

      with js_split have "{i'',j} \<in> ranking r (G \<setminus> {i}) js"
        by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

      with \<open>{i',j} \<in> ranking r (G \<setminus> {i}) js\<close> \<open>i'' \<noteq> i'\<close> \<open>i' \<noteq> j\<close> have "\<not>matching (ranking r (G \<setminus> {i}) js)"
        unfolding matching_def
        by fast

      with \<open>matching (ranking r (G \<setminus> {i}) js)\<close> show False
        by blast
    qed

    have "determ_min_on_rel ?ns r = i"
    proof (intro min_on_rel_eq ballI, goal_cases)
      case 1
      from \<open>i \<notin> Vs (ranking r G pre)\<close> \<open>{i,j} \<in> G\<close> show ?case
        by blast
    next
      case (2 y)
      have "\<lbrakk>i'' \<notin> Vs (ranking r (G \<setminus> {i}) pre); {i'',j} \<in> G \<setminus> {i}\<rbrakk> \<Longrightarrow> (i',i'') \<in> r" for i''
      proof (subst **[symmetric], intro min_on_rel_least, goal_cases)
        case 1
        from preorder \<open>j \<in> R\<close> show ?case
          by (auto intro: total_preorder_on'_subset[OF _ unmatched_neighbors_L]
              dest: total_preorder_on_imp_total_preorder_on' remove_vertices_subgraph')
      next
        case 2
        then show ?case
          by (auto intro: finite_unmatched_neighbors dest: remove_vertices_subgraph')
      qed blast+

      with 2 preorder \<open>(i,i') \<in> r\<close> \<open>i \<in> L\<close> show ?case
        unfolding *
        by (auto dest!: total_preorder_on_imp_total_preorder_on' total_preorder_on'_imp_preorder_on'
                 dest: preorder_on'_transD transD preorder_on'_refl_on'D refl_on'D)
    next
      case (3 y)
      have "y \<notin> Vs (ranking r G pre) \<Longrightarrow> {y, j} \<in> G \<Longrightarrow> i \<noteq> y \<Longrightarrow> (y, i) \<in> r \<Longrightarrow> False"
      proof -
        assume "y \<notin> Vs (ranking r G pre)" "{y,j} \<in> G" "i \<noteq> y" "(y,i) \<in> r"

        with 3 * have "y \<in> ?ns'"
          by auto

        with preorder \<open>j \<in> R\<close> have i'_leq: "(determ_min_on_rel ?ns' r, y) \<in> r"
          by (intro min_on_rel_least)
             (auto dest: total_preorder_on_imp_total_preorder_on' remove_vertices_subgraph' intro!: total_preorder_on'_subset[OF _ unmatched_neighbors_L])

        from bipartite_graph \<open>j \<in> R\<close> \<open>{y,j} \<in> G\<close> have "y \<in> L"
          by (auto dest: bipartite_edgeD)

        with preorder \<open>i \<in> L\<close> \<open>i' \<in> L\<close> \<open>(y,i) \<in> r\<close> \<open>(i,i') \<in> r\<close> \<open>(i',i) \<notin> r\<close> have "(i',y) \<notin> r"
          by (auto dest: total_preorder_on_imp_total_preorder_on' total_preorder_on'_imp_preorder_on'
                         preorder_on'_transD transD)

        with i'_leq ** show False
          by blast
      qed
      with 3 show ?case
        by auto
    qed

    with False \<open>{i,j} \<in> G\<close> \<open>i' \<in> ?ns'\<close> j_unmatched_pre have "step r G (ranking r G pre) j = insert {i,j} (ranking r G pre)"
      by (auto simp: step_def)

    with js_split show ?thesis
      by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  qed
qed

lemma dominance_order_unmatched:
  assumes preorder: "total_preorder_on L r"

  assumes "i \<in> L"
  assumes "j \<in> set js"
  assumes "set js \<subseteq> R"

  assumes "{i,j} \<in> G"
  assumes "j \<notin> Vs (ranking r (G \<setminus> {i}) js)"
  shows "i \<in> Vs (ranking r G js)"
proof -
  from \<open>j \<in> set js\<close> obtain pre suff where js_split: "js = pre @ j # suff"
    by (auto dest: split_list)

  from \<open>j \<in> set js\<close> \<open>set js \<subseteq> R\<close> have "j \<in> R"
    by blast

  with \<open>i \<in> L\<close> have "i \<noteq> j"
    by auto

  from js_split \<open>j \<notin> Vs (ranking r (G \<setminus> {i}) js)\<close> have j_not_pre:  "j \<notin> Vs (ranking r (G \<setminus> {i}) pre)"
    by (auto simp: ranking_append dest: ranking_mono_vs)

  show ?thesis
  proof (cases "i \<in> Vs (ranking r G pre)")
    case True
    with js_split show ?thesis
      by (auto simp: ranking_append dest: ranking_mono_vs)
  next
    case False
    note i_not_pre = this

    with assms js_split have pre_eq: "ranking r (G \<setminus> {i}) pre = ranking r G pre"
      by (intro ranking_remove_unmatched_eq) auto

    have "step r G (ranking r G pre) j = insert {i,j} (ranking r G pre)"
    proof (intro step_insertI, goal_cases)
      case 1
      from False \<open>{i,j} \<in> G\<close> show ?case
        by blast
    next
      case 2
      from j_not_pre show ?case
        by (simp add: pre_eq)
    next
      case 3
      then show ?case
      proof (cases "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}} = {}")
        case True
        with False \<open>{i,j} \<in> G\<close> have only_i: "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G} = {i}"
          apply (auto simp: pre_eq)
          by (metis \<open>i \<noteq> j\<close> disjoint_insert(1) empty_iff in_remove_verticesI inf_bot_right insert_iff)

        with preorder \<open>i \<in> L\<close> show ?thesis
          by (subst only_i, intro min_on_rel_singleton[symmetric])
             (auto dest: total_preorder_on_imp_total_preorder_on' total_preorder_on'_imp_preorder_on' preorder_on'_refl_on'D intro: refl_on'_subset)
      next
        case False
        show ?thesis
        proof (rule ccontr)
          let ?ns = "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G}"
          and ?ns' = "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}"
          let ?i' = "determ_min_on_rel ?ns r"

          assume "i \<noteq> ?i'"

          from preorder i_not_pre \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have "?i' \<in> ?ns"
            by (intro min_if_finite)
               (auto intro: total_preorder_on'_subset[OF _ unmatched_neighbors_L]
                     dest: total_preorder_on_imp_total_preorder_on' total_preorder_on'_imp_preorder_on')

          from preorder i_not_pre \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have *: "\<forall>x\<in>?ns. (?i',x) \<in> r \<and> (?i' \<noteq> x \<and> (x,?i') \<in> r \<longrightarrow> ?i' < x)"
            by (intro min_if_finite)
               (auto intro: total_preorder_on'_subset[OF _ unmatched_neighbors_L]
                     dest: total_preorder_on_imp_total_preorder_on' total_preorder_on'_imp_preorder_on')

          have arg_min': "determ_min_on_rel ?ns' r = ?i'"
          proof (intro min_on_rel_eq ballI, goal_cases)
            case 1
            from \<open>?i' \<in> ?ns\<close> \<open>i \<noteq> ?i'\<close> \<open>i \<noteq> j\<close> show ?case
              by (auto simp: pre_eq intro: in_remove_verticesI)
          next
            case (2 y)
            with preorder \<open>j \<in> R\<close> show ?case
              by (auto simp: pre_eq
                          intro!: min_on_rel_least total_preorder_on'_subset[OF _ unmatched_neighbors_L]
                          dest: total_preorder_on_imp_total_preorder_on' remove_vertices_subgraph')
          next
            case (3 y)
            with * show ?case
              by (auto simp: pre_eq dest: remove_vertices_subgraph')
          qed

        with False j_not_pre have "step r (G \<setminus> {i}) (ranking r (G \<setminus> {i}) pre) j = insert {?i',j} (ranking r (G \<setminus> {i}) pre)"
          by (intro step_insertI) auto

        with js_split have "j \<in> Vs (ranking r (G \<setminus> {i}) js)"
          by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)

        with \<open>j \<notin> Vs (ranking r (G \<setminus> {i}) js)\<close> show False
          by blast
      qed
    qed
  qed

  with js_split show ?thesis
    by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  qed
qed

lemma dominance_order:
  assumes preorder: "total_preorder_on L r"

  assumes "i \<in> L" "j \<in> R"
  assumes "set js = R"
  assumes "{i,j} \<in> G"

  defines "i' \<equiv> (THE i'. {i',j} \<in> ranking r (G \<setminus> {i}) js)"
  assumes "j \<in> Vs (ranking r (G \<setminus> {i}) js) \<Longrightarrow>  (i,i') \<in> r \<and> (i',i) \<notin> r"
  shows "i \<in> Vs (ranking r G js)"
proof (cases "j \<in> Vs (ranking r (G \<setminus> {i}) js)")
  case True
  then obtain e where e: "e \<in> ranking r (G \<setminus> {i}) js" "j \<in> e"
    by (auto elim: vs_member_elim)

  interpret G': graph_abs "G \<setminus> {i}"
    by (rule graph_abs_subgraph[of G])
       (auto simp: graph_abs_axioms dest: remove_vertices_subgraph')

  have "e \<in> G \<setminus> {i}"
    by (rule ranking_subgraph')
       (use preorder e \<open>set js = R\<close> in \<open>auto dest: remove_vertices_subgraph'\<close>)
  
  with \<open>j \<in> e\<close> G'.graph obtain i' where "e = {i',j}"
    by fast

  from G'.graph preorder \<open>j \<in> R\<close> \<open>set js = R\<close> have "matching (ranking r (G \<setminus> {i}) js)"
    thm neighbors_right_subset_left
    by (auto intro!: matching_ranking intro!: preorder_on'_subset[OF _ neighbors_right_subset_left]
             dest: total_preorder_on_imp_total_preorder_on' total_preorder_on'_imp_preorder_on' remove_vertices_subgraph')

  with e \<open>e = {i',j}\<close> have the_i': "(THE i'. {i',j} \<in> ranking r (G \<setminus> {i}) js) = i'"
    by (auto dest: the_match)

  from assms True e \<open>e = {i',j}\<close> show ?thesis
    by (intro dominance_order_matched) (auto simp: the_i')
next
  case False
  with assms show ?thesis
    by (auto intro: dominance_order_unmatched)
qed

lemma monotonicity_order_step:
  assumes "i \<in> L" "j \<in> R"

  assumes "j \<notin> Vs M" "j \<notin> Vs M'"

  assumes preorder: "total_preorder_on' {i. {i, j} \<in> G} r"
  assumes subset_before: "L - {i} - Vs M' \<subseteq> L - Vs M"
  shows "L - {i} - Vs (step r (G \<setminus> {i}) M' j) \<subseteq> L - Vs (step r G M j)"
  using preorder finite_vs
proof (cases rule: step_cases[where M = M])
  case no_neighbor
  with bipartite_graph subset_before \<open>i \<in> L\<close> \<open>j \<in> R\<close> have "{i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} = {}"
    apply auto
    by (smt (verit, best) Diff_iff bipartite_edgeD(4) edges_are_Vs(1) remove_vertices_not_vs remove_vertices_subgraph' subset_iff)

  with no_neighbor subset_before show ?thesis
    by (simp add: step_def)
next
  case new_match
  note new_match_orig = this

  let ?ns = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  let ?ns' = "{i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}}"
  let ?min = "determ_min_on_rel ?ns r"

  from new_match have min_available_if: "?min \<notin> Vs M' \<Longrightarrow> ?min \<noteq> i \<Longrightarrow> ?min \<in> ?ns'"
    apply (auto intro!: in_remove_verticesI)
    by (metis assms(1) assms(2) bipartite_graph bipartite_vertex(1) edges_are_Vs(2))

  from bipartite_graph \<open>j \<in> R\<close> have ns_subset_L: "?ns \<subseteq> L" and ns'_subset_L: "?ns' \<subseteq> L"
    by (auto dest: bipartite_edgeD remove_vertices_subgraph')

  with subset_before have "?ns' \<subseteq> ?ns"
    apply (auto dest: remove_vertices_subgraph')
    by (smt (verit) Diff_iff assms(2) bipartite_edgeD(4) bipartite_graph edges_are_Vs(1) in_mono remove_vertices_not_vs' remove_vertices_subgraph')

  from preorder have "total_preorder_on' {i'. {i', j} \<in> G \<setminus> {i}} r" "finite (Vs (G \<setminus> {i}))"
    by (auto intro: total_preorder_on'_subset dest: remove_vertices_subgraph')

  then show ?thesis
  proof (cases rule: step_cases[where M = M'])
    case no_neighbor

    with min_available_if subset_before new_match show ?thesis
      apply (auto simp add: step_def vs_insert)
      by (meson assms(2) bipartite_graph bipartite_vertex(1) edges_are_Vs(2))
  next
    case j_matched
    with \<open>j \<notin> Vs M'\<close> show ?thesis
      by blast
  next
    case new_match

    let ?min' = "determ_min_on_rel {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} r"

    from new_match \<open>?ns' \<subseteq> ?ns\<close> have "?min' \<in> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
      by (auto dest: remove_vertices_subgraph')

    have "?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} \<Longrightarrow> ?min = ?min'"
    proof (intro min_on_rel_eq[symmetric], goal_cases)
      case 1
      then show ?case
        by blast
    next
      case 2
      then show ?case
      proof (intro ballI min_on_rel_least, goal_cases)
        case (1 y)
        from preorder show ?case
          by (auto intro: total_preorder_on'_subset)
      next
        case (2 y)
        show ?case
          by blast
      next
        case (3 y)
        then show ?case
          using new_match_orig by blast
      next
        case (4 y)
        with \<open>?ns' \<subseteq> ?ns\<close> show ?case
          by blast
      qed
    next
      case 3
      with new_match_orig \<open>?ns' \<subseteq> ?ns\<close> show ?case
        by blast
    qed

    with new_match new_match_orig subset_before min_available_if show ?thesis
      by (auto simp: step_def vs_insert)
  qed
qed (use \<open>j \<notin> Vs M\<close> in blast)

lemma monotonicity_order_ranking:
  assumes "i \<in> L"
  assumes "set js \<subseteq> R" "distinct js"
  assumes "set js \<inter> Vs M = {}" "set js \<inter> Vs M' = {}"
  assumes "\<forall>j \<in> set js. total_preorder_on' {i. {i,j} \<in> G} r"

  assumes "L - {i} - Vs M' \<subseteq> L - Vs M"
  shows "L - {i} - (Vs (ranking' r (G \<setminus> {i}) M' js)) \<subseteq> L - (Vs (ranking' r G M js))"
  using assms
proof (induction js arbitrary: M' M)
  case (Cons j js)

  from Cons.prems have mono_step: "L - {i} - Vs (step r (G \<setminus> {i}) M' j) \<subseteq> L - Vs (step r G M j)"
    by (intro monotonicity_order_step) auto

  from Cons.prems have j'_not_in_step: "j' \<in> set js \<Longrightarrow> j' \<notin> Vs (step r G M j)" for j'
    by (intro unmatched_R_in_step_if) auto

  from Cons.prems have "j' \<in> set js \<Longrightarrow> j' \<notin> Vs (step r (G \<setminus> {i}) M' j)" for j'
    by (intro unmatched_R_in_step_if)
       (auto intro: total_preorder_on'_subset dest: remove_vertices_subgraph')

  with Cons.prems mono_step j'_not_in_step show ?case
    by (simp only: ranking_Cons, intro Cons.IH unmatched_R_in_step_if)
       auto
qed simp

lemma monotonicity_order_matched_matched:
  assumes preorder: "total_preorder_on L r"
  assumes "{i,j} \<in> G"
  assumes "i \<in> L" "j \<in> set js"
  assumes "set js \<subseteq> R" "distinct js"
  assumes "set js \<inter> Vs M = {}" "set js \<inter> Vs M' = {}"
  
  assumes "j \<notin> Vs M" "j \<notin> Vs M'"
  assumes "L - {i} - Vs M' \<subseteq> L - Vs M"

  assumes "matching M" "matching M'"

  assumes i'j: "{i',j} \<in> ranking' r G M js"
  assumes i''j: "{i'',j} \<in> (ranking' r (G \<setminus> {i}) M' js)"
  shows "(i', i'') \<in> r"
  using assms
proof -
  from \<open>j \<in> set js\<close> \<open>distinct js\<close> obtain pre suff where js_decomp: "js = pre @ j # suff" "j \<notin> set pre" "j \<notin> set suff"
    by (auto dest: split_list_distinct)

  from \<open>j \<in> set js\<close> \<open>set js \<subseteq> R\<close> have "j \<in> R"
    by blast

  let ?ranking_pre = "ranking' r G M pre"
  and ?ranking_pre' = "ranking' r (G \<setminus> {i}) M' pre"

  from js_decomp assms have "L - {i} - Vs ?ranking_pre' \<subseteq> L - Vs ?ranking_pre"
    by (intro monotonicity_order_ranking) auto

  from preorder js_decomp \<open>set js \<subseteq> R\<close> \<open>j \<notin> Vs M\<close> have j_unmatched_pre: "j \<notin> Vs ?ranking_pre"
    by (intro unmatched_R_in_ranking_if) auto

  let ?ns = "{i. i \<notin> Vs ?ranking_pre \<and> {i,j} \<in> G}"
  let ?min = "determ_min_on_rel ?ns r"

  have "?ns \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns = {}"
    then have "step r G ?ranking_pre j = ?ranking_pre"
      by (simp add: step_def)

    with preorder j_unmatched_pre js_decomp \<open>set js \<subseteq> R\<close> have "j \<notin> Vs (ranking' r G M js)"
      by (simp only: ranking_append ranking_Cons)
         (rule unmatched_R_in_ranking_if, auto)

    with i'j show False
      by (auto dest: edges_are_Vs)
  qed

  with preorder \<open>j \<in> R\<close> have "?min \<in> ?ns"
    by (intro min_if_finite)
       (auto intro: total_preorder_on'_subset)
    
  with j_unmatched_pre have "step r G ?ranking_pre j = insert {?min, j} ?ranking_pre"
    by (auto simp: step_def)
  
  with js_decomp have "{?min, j} \<in> ranking' r G M js"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

  with i'j preorder \<open>set js \<subseteq> R\<close> \<open>matching M\<close> have "i' = ?min"
    by (auto intro: matching_partner_eqI matching_ranking)



  from preorder js_decomp \<open>set js \<subseteq> R\<close> \<open>j \<notin> Vs M'\<close> have j_unmatched_pre': "j \<notin> Vs ?ranking_pre'"
    by (intro unmatched_R_in_ranking_if)
       (auto dest: remove_vertices_subgraph')

  let ?ns' = "{i'. i' \<notin> Vs ?ranking_pre' \<and> {i',j} \<in> G \<setminus> {i}}"
  let ?min' = "determ_min_on_rel ?ns' r"

  have "?ns' \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns' = {}"
    then have "step r (G \<setminus> {i}) ?ranking_pre' j = ?ranking_pre'"
      by (simp add: step_def)

    with preorder j_unmatched_pre' js_decomp \<open>set js \<subseteq> R\<close> have "j \<notin> Vs (ranking' r (G \<setminus> {i}) M' js)"
      by (simp only: ranking_append ranking_Cons)
         (rule unmatched_R_in_ranking_if, auto dest: remove_vertices_subgraph')

    with i''j show False
      by (auto dest: edges_are_Vs)
  qed

  with preorder \<open>j \<in> R\<close> have "?min' \<in> ?ns'"
    by (intro min_if_finite)
       (auto dest: remove_vertices_subgraph' 
             intro: total_preorder_on'_subset)

  with j_unmatched_pre' have "step r (G \<setminus> {i}) ?ranking_pre' j = insert {?min', j} ?ranking_pre'"
    by (auto simp: step_def)

  with js_decomp have "{?min', j} \<in> ranking' r (G \<setminus> {i}) M' js"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

  with preorder \<open>set js \<subseteq> R\<close> \<open>matching M'\<close> have "i'' = ?min'"
    by (auto intro: matching_partner_eqI[OF _ i''j] matching_ranking
             dest: remove_vertices_subgraph')

  from \<open>?min' \<in> ?ns'\<close> have "?min' \<in> ?ns"
    apply (auto dest: remove_vertices_subgraph')
    apply (smt (verit) DiffE DiffI \<open>L - {i} - Vs (ranking' r (G \<setminus> {i}) M' pre) \<subseteq> L - Vs (ranking' r G M pre)\<close> \<open>j \<in> R\<close> bipartite_edgeD(4) bipartite_graph edges_are_Vs(1) remove_vertices_not_vs remove_vertices_subgraph' subsetD)
    done

  with preorder \<open>?min \<in> ?ns\<close> \<open>j \<in> R\<close> have "(?min, ?min') \<in> r"
    by (intro min_on_rel_least)
       (auto dest: total_preorder_on_imp_total_preorder_on' intro: total_preorder_on'_subset)

  with \<open>i' = ?min\<close> \<open>i'' = ?min'\<close> show "(i',i'') \<in> r"
    by simp
qed

lemma min_on_rel_Restr:
  assumes "total_preorder_on' S r"
  assumes "finite S"  "S \<noteq> {}"
  assumes "S \<subseteq> T"
  shows "determ_min_on_rel S (Restr r T) = determ_min_on_rel S r"
  using assms
  by (intro min_on_rel_eq)
     (auto dest: min_if_finite)

lemma step_Restr_to_vertices:
  assumes "j \<in> R"
  assumes preorder: "total_preorder_on' L r"
  shows "step (Restr r (L - X)) (G \<setminus> X) M j = step r (G \<setminus> X) M j"
proof (cases M j "G \<setminus> X" rule: step_cases')
  case new_match
  let ?ns = "{i. i \<notin> Vs M \<and> {i, j} \<in> G \<setminus> X}"
  from bipartite_graph \<open>j \<in> R\<close> have "?ns \<subseteq> L - X"
    by (auto dest: remove_vertices_subgraph' bipartite_edgeD edges_are_Vs intro: remove_vertices_not_vs')

  with new_match preorder have "determ_min_on_rel ?ns (Restr r (L - X)) = determ_min_on_rel ?ns r"
    by (intro min_on_rel_Restr)
       (auto intro: total_preorder_on'_subset)

  with new_match show ?thesis
    by (simp add: step_def)
qed (simp_all add: step_def)

lemma ranking_Restr_to_vertices:
  assumes "set js \<subseteq> R"
  assumes "total_preorder_on' L r"
  shows "ranking' (Restr r (L - X)) (G \<setminus> X) M js = ranking' r (G \<setminus> X) M js"
  using assms
  by (induction js arbitrary: M) (simp_all add: ranking_Cons step_Restr_to_vertices)

end
end
