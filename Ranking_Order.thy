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


lemma refl_on'D: "refl_on' S r \<Longrightarrow> a \<in> S \<Longrightarrow> (a,a) \<in> r"
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

lemma min_rel_linorder_eq:
  assumes "linorder_on' {x. P x} r"
  assumes "P a"
  assumes "\<forall>y. P y \<longrightarrow> (a,y) \<in> r"
  shows "min_rel P r = a"
  unfolding min_rel_def is_min_rel_def
  by (rule someI2[of _ a])
     (use assms in \<open>auto simp add: antisym_def linorder_on'_def\<close>)

lemma min_on_rel_linorder_eq:
  assumes "linorder_on' S r"
  assumes "a \<in> S"
  assumes "\<forall>y\<in>S. (a,y) \<in> r"
  shows "min_on_rel S r = a"
  using assms
  unfolding min_on_rel_def
  by (auto intro: min_rel_linorder_eq)

lemma min_on_rel_singleton:
  shows "min_on_rel {a} r = a"
  by (auto simp: min_on_rel_def min_rel_def is_min_rel_def)

lemma min_on_rel_least:
  assumes "linorder_on' S r"
  assumes S: "finite S" "S \<noteq> {}"
  assumes "y \<in> S"
  shows "(min_on_rel S r, y) \<in> r"
  using S assms
proof (induction S arbitrary: y rule: finite_induct)
  case (insert s S)

  show ?case
  proof (cases "S = {}")
    case True
    with insert.prems show ?thesis
      by (auto simp: min_on_rel_singleton linorder_on'_def refl_on'_def)
  next
    case False
    let ?min = "min_on_rel S r"

    from insert.prems False have IH: "y' \<in> S \<Longrightarrow> (?min, y') \<in> r" for y'
      by (intro insert.IH) (auto intro: linorder_on'_subset)

    from False insert.prems have "?min \<in> S"
      by (auto intro: min_if_finite linorder_on'_imp_preorder_on' dest: linorder_on'_subset)

    with insert.prems
    consider (less) "(s, ?min) \<in> r" "(?min, s) \<notin> r" | (eq) "(s, ?min) \<in> r" "(?min, s) \<in> r" | (gt) "(s, ?min) \<notin> r" "(?min, s) \<in> r"
      unfolding total_on_def linorder_on'_def refl_on'_def
      by force

    then show ?thesis
    proof cases
      case less
      with insert.prems have "min_on_rel (insert s S) r = s"
        by (intro min_on_rel_linorder_eq)
           (auto dest: linorder_on'_refl_on'D refl_on'D linorder_on'_transD IH transD)

      with insert.prems less show ?thesis
        by (auto dest: linorder_on'_refl_on'D refl_on'D linorder_on'_transD IH transD)
    next
      case eq
      with insert.prems \<open>?min \<in> S\<close> \<open>s \<notin> S\<close> have "min_on_rel (insert s S) r = s"
        by (auto dest!: linorder_on'_antisymD simp: antisym_def) blast+

      with insert.prems eq show ?thesis
        by (auto dest: linorder_on'_refl_on'D refl_on'D linorder_on'_transD IH transD)
    next
      case gt
      with insert.prems \<open>?min \<in> S\<close> have "min_on_rel (insert s S) r = ?min"
        by (intro min_on_rel_linorder_eq) (auto dest: IH)

      with insert.prems gt show ?thesis
        by (auto dest: IH)
    qed
  qed
qed blast

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

lemma step_insertI:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {}" "j \<notin> Vs M"
  assumes "i = min_on_rel {i. i \<notin> Vs M \<and> {i,j} \<in> G} r"
  shows "step r G M j = insert {i,j} M"
  using assms
  by (simp add: step_def)

lemma step_subgraph:
  assumes fin: "finite (Vs G)"
  assumes preorder: "preorder_on' {i. {i,j} \<in> G} r"
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
  fixes L :: "'a set" and R :: "'a set"
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

lemma preorder_on_neighborsI[intro]:
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
  assumes "j \<in> R"
  shows "preorder_on' {i. {i,j} \<in> H} r"
  using assms
  by (auto dest: preorder_on_imp_preorder_on' neighbors_right_subset_left intro: preorder_on'_subset)

lemma linorder_on_neighborsI[intro]:
  assumes "H \<subseteq> G"
  assumes "linorder_on L r"
  assumes "j \<in> R"
  shows "linorder_on' {i. {i,j} \<in> H} r"
  using assms
  by (auto dest: linorder_on_imp_linorder_on' neighbors_right_subset_left intro: linorder_on'_subset)

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
  assumes "preorder_on' {i. {i,j} \<in> H} r"
  assumes "j \<in> R"
  assumes "i \<notin> Vs M" "{i,j} \<in> H"
  shows "min_on_rel {i. i \<notin> Vs M \<and> {i, j} \<in> H} r \<in> L" (is "min_on_rel ?S r \<in> L")
proof -
  from assms have "min_on_rel ?S r \<in> ?S"
    by (intro min_if_finite finite_unmatched_neighbors)
       (auto intro: preorder_on'_subset)

  with \<open>H \<subseteq> G\<close> \<open>j \<in> R\<close> bipartite_graph show ?thesis
    by (auto dest: bipartite_edgeD bipartite_subgraph)
qed

lemma unmatched_R_in_step_if:
  assumes "H \<subseteq> G"
  assumes preorder: "preorder_on' {i. {i,j'} \<in> H} r"
  assumes "j' \<in> R" "j' \<noteq> j"
  assumes "j \<notin> L" "j \<notin> Vs M"
  shows "j \<notin> Vs (step r H M j')"
  using assms
  by (cases M j' H rule: step_cases')
     (auto simp: step_def vs_insert dest: min_in_L)

lemma unmatched_R_in_ranking_if:
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
  assumes "set js \<subseteq> R"
  assumes "j \<notin> L" "j \<notin> set js"
  assumes "j \<notin> Vs M"
  shows "j \<notin> Vs (ranking' r H M js)"
  using assms
proof (induction js arbitrary: M)
  case (Cons j' js)

  then have "j \<notin> Vs (step r H M j')"
    by (intro unmatched_R_in_step_if preorder_on_neighborsI preorders_onI)
       auto

  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma bipartite_step:
  assumes subgraph: "H \<subseteq> G"
  assumes preorder: "preorder_on' {i. {i,j} \<in> H} r"
  assumes "bipartite M L R"
  assumes "j \<in> R"
  shows "bipartite (step r H M j) L R"
  using preorder finite_vs_subgraph[OF subgraph]
  by (cases rule: step_cases[where M = M])
     (use assms in \<open>auto simp: step_def intro!: bipartite_insertI dest: neighbors_right_subset_left\<close>)

lemma bipartite_ranking:
  assumes "H \<subseteq> G"
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> H} r"
  assumes "set js \<subseteq> R"
  assumes "bipartite M L R"
  shows "bipartite (ranking' r H M js) L R"
  using assms
  by (induction js arbitrary: M)
     (auto simp: ranking_Cons dest: bipartite_step)

lemma ranking_subgraph:
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
  assumes "set js \<subseteq> R"
  shows "ranking r H js \<subseteq> H"
  using assms graph
  by (intro ranking_subgraph)
     (auto intro: preorder_on_neighborsI ranking_subgraph finite_vs_subgraph)

lemma ranking_subgraph':
  assumes "H \<subseteq> G"
  assumes "preorder_on L r"
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
  assumes "\<forall>j\<in>set js. preorder_on' {i. {i,j} \<in> H} r"
  assumes "matching M"
  assumes "bipartite M L R"
  assumes j_matched: "j \<in> Vs (ranking' r H M js)"
  assumes "j \<in> R"
  assumes "set js \<subseteq> R"
  shows "(THE i. {i,j} \<in> ranking' r H M js) \<in> L"
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

  with \<open>u \<in> L\<close> show ?thesis
    by blast
qed

lemma step_remove_unmatched_eq:
  assumes linorder: "linorder_on L r" \<comment> \<open>required because of \<^term>\<open>Eps\<close> in \<^term>\<open>min_on_rel\<close>\<close>

  assumes "i \<in> L" "j \<in> R"
  assumes "i \<notin> Vs (step r G M j)"
  shows "step r (G \<setminus> {i}) M j = step r G M j"
proof -
  from linorder \<open>j \<in> R\<close> have "preorder_on' {i. {i,j} \<in> G} r"
    by (auto dest: linorder_on_imp_preorder_on)

  from this finite_vs
  show ?thesis
  proof (cases rule: step_cases[where M = M])
    case new_match
    let ?ns = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G}"
    and ?ns' = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G \<setminus> {i}}"

    let ?min = "min_on_rel ?ns r"
    and ?min' = "min_on_rel ?ns' r"

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
    proof (intro min_on_rel_linorder_eq, goal_cases)
      case 1
      from linorder \<open>?ns' \<subseteq> L\<close> show ?case
        by (auto dest: linorder_on_imp_linorder_on' intro: linorder_on'_subset)
    next
      case 2
      from \<open>?min \<in> ?ns\<close> \<open>?min \<noteq> i\<close> \<open>j \<noteq> i\<close> show ?case
        by (auto intro: in_remove_verticesI)
    next
      case 3
      from \<open>?ns' \<subseteq> ?ns\<close> \<open>preorder_on' {i. {i,j} \<in> G} r\<close> show ?case
      proof (intro ballI min_on_rel_least, goal_cases)
        case 1
        from linorder \<open>?ns \<subseteq> L\<close> show ?case
          by (auto dest: linorder_on_imp_linorder_on' intro: linorder_on'_subset)
      next
        case 2
        show ?case
          by (auto intro: finite_subset)
      next
        case 3
        from new_match show ?case by blast
      next
        case (4 y)
        with \<open>?ns' \<subseteq> ?ns\<close> show ?case
          by blast
      qed
    qed

    with \<open>j \<notin> Vs M\<close> \<open>?ns' \<noteq> {}\<close> show ?thesis
      by (subst step_eq) (simp add: step_def)
  qed (use assms in \<open>auto simp: step_def dest: remove_vertices_subgraph'\<close>)
qed

lemma ranking_remove_unmatched_eq:
  assumes linorder: "linorder_on L r"

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
  assumes linorder: "linorder_on L r"

  assumes "i \<in> L" "j \<in> R"
  assumes "set js = R"
  assumes "{i,j} \<in> G"

  assumes "{i',j} \<in> ranking r (G \<setminus> {i}) js"
  assumes less: "(i,i') \<in> r" "(i',i) \<notin> r"
  shows "i \<in> Vs (ranking r G js)"
proof -
  from \<open>set js = R\<close> \<open>j \<in> R\<close> obtain pre suff where js_split: "js = pre @ j # suff" "j \<notin> set pre"
    by (auto dest: split_list_first)

  with linorder \<open>set js = R\<close> \<open>j \<in> R\<close>
  have j_unmatched_pre: "j \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> j \<notin> Vs (ranking r G pre)"
    by (intro unmatched_R_in_ranking_if conjI)
       (auto dest: remove_vertices_subgraph' linorder_on_imp_preorder_on)

  from linorder \<open>set js = R\<close> have preorder_neighbors:
    "j' \<in> set js \<Longrightarrow> preorder_on' {i'. {i', j'} \<in> G \<setminus> {i}} r" for j'
    by (auto dest: linorder_on_imp_preorder_on remove_vertices_subgraph')

  with \<open>set js = R\<close> linorder have bipartite_js: "bipartite (ranking r (G \<setminus> {i}) js) L R"
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

  from linorder \<open>set js = R\<close> have "{i',j} \<in> G \<setminus> {i}"
    by (auto dest: linorder_on_imp_preorder_on remove_vertices_subgraph' 
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

    have **: "min_on_rel ?ns' r = i'"
    proof (rule ccontr)
      assume "min_on_rel ?ns' r \<noteq> i'"
      then obtain i'' where i'': "i'' = min_on_rel ?ns' r" "i'' \<noteq> i'"
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

    have "min_on_rel ?ns r = i"
    proof (intro min_on_rel_linorder_eq ballI, goal_cases)
      case 1
      from linorder \<open>j \<in> R\<close> show ?case
        by (auto intro: linorder_on'_subset[OF _ unmatched_neighbors_L] unmatched_neighbors_L
                 dest: linorder_on_imp_linorder_on')
    next
      case 2
      from \<open>i \<notin> Vs (ranking r G pre)\<close> \<open>{i,j} \<in> G\<close> show ?case
        by blast
    next
      case (3 y)
      have "\<lbrakk>i'' \<notin> Vs (ranking r (G \<setminus> {i}) pre); {i'',j} \<in> G \<setminus> {i}\<rbrakk> \<Longrightarrow> (i',i'') \<in> r" for i''
      proof (subst **[symmetric], intro min_on_rel_least, goal_cases)
        case 1
        from linorder \<open>j \<in> R\<close> show ?case
          by (auto intro: linorder_on'_subset[OF _ unmatched_neighbors_L]
                   dest: linorder_on_imp_linorder_on' remove_vertices_subgraph')
      next
        case 2
        then show ?case
          by (auto intro: finite_unmatched_neighbors dest: remove_vertices_subgraph')
      qed blast+

      with 3 linorder \<open>(i,i') \<in> r\<close> \<open>i \<in> L\<close> show ?case
        unfolding *
        by (auto dest: linorder_on_imp_linorder_on' linorder_on'_transD transD linorder_on'_refl_on'D refl_on'D)
    qed

    with False \<open>{i,j} \<in> G\<close> \<open>i' \<in> ?ns'\<close> j_unmatched_pre have "step r G (ranking r G pre) j = insert {i,j} (ranking r G pre)"
      by (auto simp: step_def)

    with js_split show ?thesis
      by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  qed
qed

lemma dominance_order_unmatched:
  assumes linorder: "linorder_on L r"

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
        with False \<open>{i,j} \<in> G\<close> have "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G} = {i}"
          apply (auto simp: pre_eq)
          by (metis \<open>i \<noteq> j\<close> disjoint_insert(1) empty_iff in_remove_verticesI inf_bot_right insert_iff)

        then show ?thesis
          by simp (intro min_on_rel_singleton[symmetric])
      next
        case False
        show ?thesis
        proof (rule ccontr)
          let ?ns = "{i. i \<notin> Vs (ranking r G pre) \<and> {i,j} \<in> G}"
          and ?ns' = "{i'. i' \<notin> Vs (ranking r (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}"
          let ?i' = "min_on_rel ?ns r"

          assume "i \<noteq> ?i'"

          from linorder i_not_pre \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have "?i' \<in> ?ns"
            by (intro min_if_finite)
               (auto intro: preorder_on'_subset[OF _ unmatched_neighbors_L]
                     dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on')

          have arg_min': "min_on_rel ?ns' r = ?i'"
          proof (intro min_on_rel_linorder_eq ballI, goal_cases)
            case 1
            from linorder \<open>j \<in> R\<close> show ?case
              by (auto intro: linorder_on'_subset[OF _ unmatched_neighbors_L]
                  dest: linorder_on_imp_linorder_on' remove_vertices_subgraph')
          next
            case 2
            from \<open>?i' \<in> ?ns\<close> \<open>i \<noteq> ?i'\<close> \<open>i \<noteq> j\<close> show ?case
              by (auto simp: pre_eq intro: in_remove_verticesI)
          next
            case (3 y)
            with linorder \<open>j \<in> R\<close> show ?case
              by (auto simp: pre_eq 
                       intro!: min_on_rel_least finite_unmatched_neighbors linorder_on'_subset[OF _ unmatched_neighbors_L]
                       dest: remove_vertices_subgraph' linorder_on_imp_linorder_on')
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
  assumes linorder: "linorder_on L r"

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
       (use linorder e \<open>set js = R\<close> in \<open>auto dest: remove_vertices_subgraph' linorder_on_imp_preorder_on preorder_on_imp_preorder_on'\<close>)
  
  with \<open>j \<in> e\<close> G'.graph obtain i' where "e = {i',j}"
    by fast

  from G'.graph linorder \<open>j \<in> R\<close> \<open>set js = R\<close> have "matching (ranking r (G \<setminus> {i}) js)"
    thm neighbors_right_subset_left
    by (auto intro!: matching_ranking intro!: preorder_on'_subset[OF _ neighbors_right_subset_left]
             dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on' remove_vertices_subgraph')

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

  assumes linorder: "linorder_on' {i. {i, j} \<in> G} r"
  assumes subset_before: "L - {i} - Vs M' \<subseteq> L - Vs M"
  shows "L - {i} - Vs (step r (G \<setminus> {i}) M' j) \<subseteq> L - Vs (step r G M j)"
  using linorder_on'_imp_preorder_on'[OF linorder] finite_vs
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

  let ?min = "min_on_rel {i. i \<notin> Vs M \<and> {i,j} \<in> G} r"

  from new_match have min_available_if: "?min \<notin> Vs M' \<Longrightarrow> ?min \<noteq> i \<Longrightarrow> ?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}}"
    apply (auto intro!: in_remove_verticesI)
    by (metis assms(1) assms(2) bipartite_graph bipartite_vertex(1) edges_are_Vs(2))

  from linorder have "preorder_on' {i'. {i', j} \<in> G \<setminus> {i}} r" "finite (Vs (G \<setminus> {i}))"
    by (auto intro: preorder_on'_subset dest: remove_vertices_subgraph' linorder_on'_imp_preorder_on')

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

    let ?min' = "min_on_rel {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} r"

    from new_match have "?min' \<in> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
      apply (auto dest: remove_vertices_subgraph')
      by (smt (verit) DiffE DiffI assms(2) bipartite_edgeD(4) bipartite_graph edges_are_Vs(1) in_mono remove_vertices_not_vs remove_vertices_subgraph' subset_before)

    have "?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}} \<Longrightarrow> ?min = ?min'"
    proof -
      assume "?min \<in> {i'. i' \<notin> Vs M' \<and> {i',j} \<in> G \<setminus> {i}}"

      with linorder have "(?min', ?min) \<in> r"
        by (intro min_on_rel_least linorder_on'_subset[where S = "{i. {i,j} \<in> G}" and T = "{i'. i' \<notin> Vs M' \<and> {i', j} \<in> G \<setminus> {i}}"])
           (auto dest: remove_vertices_subgraph' intro: finite_vs_subgraph)

      from linorder \<open>?min' \<in> {i. i \<notin> Vs M \<and> {i,j} \<in> G}\<close> have "(?min, ?min') \<in> r"
        by (intro min_on_rel_least linorder_on'_subset[where S = "{i. {i,j} \<in> G}" and T = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"])
           (auto intro: finite_vs_subgraph)

      with linorder \<open>(?min', ?min) \<in> r\<close> show "?min = ?min'"
        unfolding linorder_on'_def antisym_def
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
  assumes "\<forall>j \<in> set js. linorder_on' {i. {i,j} \<in> G} r"

  assumes "L - {i} - Vs M' \<subseteq> L - Vs M"
  shows "L - {i} - (Vs (ranking' r (G \<setminus> {i}) M' js)) \<subseteq> L - (Vs (ranking' r G M js))"
  using assms
proof (induction js arbitrary: M' M)
  case (Cons j js)

  from Cons.prems have mono_step: "L - {i} - Vs (step r (G \<setminus> {i}) M' j) \<subseteq> L - Vs (step r G M j)"
    by (intro monotonicity_order_step) auto

  from Cons.prems have j'_not_in_step: "j' \<in> set js \<Longrightarrow> j' \<notin> Vs (step r G M j)" for j'
    by (intro unmatched_R_in_step_if)
       (auto intro: linorder_on'_imp_preorder_on')

  from Cons.prems have "j' \<in> set js \<Longrightarrow> j' \<notin> Vs (step r (G \<setminus> {i}) M' j)" for j'
    by (intro unmatched_R_in_step_if)
       (auto intro: linorder_on'_imp_preorder_on' preorder_on'_subset dest: remove_vertices_subgraph')

  with Cons.prems mono_step j'_not_in_step show ?case
    by (simp only: ranking_Cons, intro Cons.IH unmatched_R_in_step_if)
       auto
qed simp


lemma monotonicity_order_matched_matched:
  assumes linorder: "linorder_on L r"
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
    by (intro monotonicity_order_ranking) (auto intro: linorder_on_neighborsI)

  from linorder js_decomp \<open>set js \<subseteq> R\<close> \<open>j \<notin> Vs M\<close> have j_unmatched_pre: "j \<notin> Vs ?ranking_pre"
    by (intro unmatched_R_in_ranking_if)
       (auto dest: linorder_on_imp_preorder_on)

  let ?ns = "{i. i \<notin> Vs ?ranking_pre \<and> {i,j} \<in> G}"
  let ?min = "min_on_rel ?ns r"

  have "?ns \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns = {}"
    then have "step r G ?ranking_pre j = ?ranking_pre"
      by (simp add: step_def)

    with linorder j_unmatched_pre js_decomp \<open>set js \<subseteq> R\<close> have "j \<notin> Vs (ranking' r G M js)"
      by (simp only: ranking_append ranking_Cons)
         (rule unmatched_R_in_ranking_if, auto dest: linorder_on_imp_preorder_on)

    with i'j show False
      by (auto dest: edges_are_Vs)
  qed

  with linorder \<open>j \<in> R\<close> have "?min \<in> ?ns"
    by (intro min_if_finite)
       (auto dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on' intro: preorder_on_neighborsI preorder_on'_subset)
    
  with j_unmatched_pre have "step r G ?ranking_pre j = insert {?min, j} ?ranking_pre"
    by (auto simp: step_def)
  
  with js_decomp have "{?min, j} \<in> ranking' r G M js"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

  with i'j linorder \<open>set js \<subseteq> R\<close> \<open>matching M\<close> have "i' = ?min"
    by (auto intro: matching_partner_eqI matching_ranking preorder_on_neighborsI dest: linorder_on_imp_preorder_on)



  from linorder js_decomp \<open>set js \<subseteq> R\<close> \<open>j \<notin> Vs M'\<close> have j_unmatched_pre': "j \<notin> Vs ?ranking_pre'"
    by (intro unmatched_R_in_ranking_if)
       (auto dest: remove_vertices_subgraph' linorder_on_imp_preorder_on)

  let ?ns' = "{i'. i' \<notin> Vs ?ranking_pre' \<and> {i',j} \<in> G \<setminus> {i}}"
  let ?min' = "min_on_rel ?ns' r"

  have "?ns' \<noteq> {}"
  proof (rule ccontr, simp only: not_not)
    assume "?ns' = {}"
    then have "step r (G \<setminus> {i}) ?ranking_pre' j = ?ranking_pre'"
      by (simp add: step_def)

    with linorder j_unmatched_pre' js_decomp \<open>set js \<subseteq> R\<close> have "j \<notin> Vs (ranking' r (G \<setminus> {i}) M' js)"
      by (simp only: ranking_append ranking_Cons)
         (rule unmatched_R_in_ranking_if, auto dest: linorder_on_imp_preorder_on remove_vertices_subgraph')

    with i''j show False
      by (auto dest: edges_are_Vs)
  qed

  with linorder \<open>j \<in> R\<close> have "?min' \<in> ?ns'"
    by (intro min_if_finite)
       (auto dest: linorder_on_imp_preorder_on preorder_on_imp_preorder_on' remove_vertices_subgraph' 
             intro: preorder_on_neighborsI preorder_on'_subset)

  with j_unmatched_pre' have "step r (G \<setminus> {i}) ?ranking_pre' j = insert {?min', j} ?ranking_pre'"
    by (auto simp: step_def)

  with js_decomp have "{?min', j} \<in> ranking' r (G \<setminus> {i}) M' js"
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

  with linorder \<open>set js \<subseteq> R\<close> \<open>matching M'\<close> have "i'' = ?min'"
    by (auto intro: matching_partner_eqI[OF _ i''j] matching_ranking preorder_on_neighborsI
             dest: linorder_on_imp_preorder_on remove_vertices_subgraph')

  from \<open>?min' \<in> ?ns'\<close> have "?min' \<in> ?ns"
    apply (auto dest: remove_vertices_subgraph')
    apply (smt (verit) DiffE DiffI \<open>L - {i} - Vs (ranking' r (G \<setminus> {i}) M' pre) \<subseteq> L - Vs (ranking' r G M pre)\<close> \<open>j \<in> R\<close> bipartite_edgeD(4) bipartite_graph edges_are_Vs(1) remove_vertices_not_vs remove_vertices_subgraph' subsetD)
    done

  with linorder \<open>?min \<in> ?ns\<close> \<open>j \<in> R\<close> have "(?min, ?min') \<in> r"
    by (intro min_on_rel_least)
       (auto dest: linorder_on_imp_linorder_on' intro: linorder_on'_subset linorder_on_neighborsI)

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
