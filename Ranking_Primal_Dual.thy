theory Ranking_Primal_Dual
  imports 
    More_Graph
    Jordan_Normal_Form.Matrix
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

definition one_vec :: "nat \<Rightarrow> 'a :: one vec" ("1\<^sub>v") where
  "1\<^sub>v n \<equiv> vec n (\<lambda>i. 1)"

lemma one_carrier_vec[simp]: "1\<^sub>v n \<in> carrier_vec n"
  unfolding one_vec_def carrier_vec_def by simp

lemma index_one_vec[simp]: "i < n \<Longrightarrow> 1\<^sub>v n $ i = 1" "dim_vec (1\<^sub>v n) = n"
  unfolding one_vec_def by simp_all

type_synonym 'a graph = "'a set set"

lemma to_nat_on_from_nat_into_less:
  assumes "finite A"
  assumes "i < card A"
  shows "to_nat_on A (from_nat_into A i) = i"
  using assms
  by (auto intro!: to_nat_on_from_nat_into dest!: to_nat_on_finite simp: bij_betw_def)

lemma to_nat_on_less_card:
  assumes "finite A"
  assumes "a \<in> A"
  shows "to_nat_on A a < card A"
  using assms
  by (auto dest: to_nat_on_finite bij_betwE)

lemma arg_min_less_eq: fixes f :: "'a \<Rightarrow> 'b :: order"
  assumes "P a"
  assumes "\<forall>y. a \<noteq> y \<and> P y \<longrightarrow> f a < f y"
  shows "arg_min f P = a"
  unfolding arg_min_def is_arg_min_def
  by (rule someI2[of _ a]) (use assms in auto)  


\<comment> \<open>probably can define step (and ranking) here - with additional Y param. then need to construct
  primal+dual sols in the locale where mappings are defined (might need definite description again
  to select L and R vertices for alpha and beta parts)\<close>
definition step :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a graph" where
  "step Y G M j = (
    let ns = {i. i \<notin> Vs M \<and> {i,j} \<in> G} in
    if ns \<noteq> {} \<and> j \<notin> Vs M
    then let i = arg_min_on Y ns in insert {i,j} M
    else M
  )"

definition "ranking' Y G M \<equiv> foldl (step Y G) M"

abbreviation "ranking Y G \<equiv> ranking' Y G {}"

lemma step_cases[case_names no_neighbor j_matched new_match]:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {} \<Longrightarrow> j \<notin> Vs M \<Longrightarrow> P"
  shows "P"
  using assms
  by blast

lemma step_mono: "e \<in> M \<Longrightarrow> e \<in> step Y G M j"
  by (simp add: step_def)

lemma step_mono_vs: "v \<in> Vs M \<Longrightarrow> v \<in> Vs (step Y G M j)"
  by (auto simp: vs_member dest: step_mono)

lemma step_insertI:
  assumes "{i. i \<notin> Vs M \<and> {i,j} \<in> G} \<noteq> {}" "j \<notin> Vs M"
  assumes "i = arg_min_on Y {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  shows "step Y G M j = insert {i,j} M"
  using assms
  unfolding step_def
  by simp

lemma finite_unmatched_neighbors[intro]:
  "finite (Vs G) \<Longrightarrow> finite {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  by (rule finite_subset[of _ "Vs G"]) auto

lemma matching_step: 
  assumes "finite (Vs G)"

  assumes "matching M"
  shows "matching (step Y G M j)"
proof (cases "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {}")
  case False
  let ?ns = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  obtain i where i: "i = arg_min_on Y ?ns"
    by blast

  from \<open>finite (Vs G)\<close> have "finite ?ns"
    by blast

  with False i have "i \<in> ?ns"
    by (auto dest: arg_min_if_finite)

  then have "i \<notin> Vs M"
    by blast

  with assms i False show ?thesis
    by (auto intro: matching_insert simp: step_def)
qed (use assms in \<open>simp add: step_def\<close>)

lemma subgraph_step:
  assumes "finite (Vs G)"
  assumes "M \<subseteq> G"
  shows "step Y G M j \<subseteq> G"
  using step_cases[of M j G]
proof (cases)
  case new_match
  let ?ns = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match assms have "?i \<in> ?ns"
    by (intro arg_min_if_finite) blast+

  with assms show ?thesis
    by (simp add: step_def)
qed (use assms in \<open>simp_all add: step_def\<close>)

lemma step_matches_graph_edge:
  assumes "finite (Vs G)"
  assumes "e \<notin> M"
  assumes "e \<in> step Y G M j"
  shows "e \<in> G"
  using step_cases[of M j G]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match assms have "?i \<in> ?ns"
    by (intro arg_min_if_finite) blast+

  from assms new_match have "e = {?i,j}"
    by (simp add: step_def)

  with \<open>?i \<in> ?ns\<close> show ?thesis
    by blast
qed (use assms in \<open>simp_all add: step_def\<close>)

lemma bipartite_step:
  assumes "finite (Vs G)"

  assumes "bipartite G L R"
  assumes "M \<subseteq> G"
  shows "bipartite (step Y G M j) L R"
  using assms
  by (auto dest: subgraph_step intro: bipartite_subgraph)

lemma edge_in_step:
  assumes "e \<in> step Y G M j"
  shows "e \<in> M \<or> j \<in> e"
  using assms
  by (auto simp: step_def split: if_splits)

lemma ranking_Nil[simp]: "ranking' Y G M [] = M"
  unfolding ranking'_def by simp

lemma ranking_Cons: "ranking' Y G M (j#js) = ranking' Y G (step Y G M j) js"
  unfolding ranking'_def
  by simp

lemma ranking_append: "ranking' Y G M (xs@ys) = ranking' Y G (ranking' Y G M xs) ys"
  unfolding ranking'_def
  by simp

lemma ranking_mono: "e \<in> M \<Longrightarrow> e \<in> ranking' Y G M js"
  by (induction js arbitrary: M) (auto simp add: ranking'_def step_mono)

lemma ranking_mono_vs: "v \<in> Vs M \<Longrightarrow> v \<in> Vs (ranking' Y G M js)"
  by (auto simp: vs_member dest: ranking_mono)

lemma matching_ranking:
  assumes "finite (Vs G)"

  assumes "matching M"
  shows "matching (ranking' Y G M js)"
  using assms
  by (induction js arbitrary: M)
     (auto dest: matching_step simp: ranking_Cons)

lemma subgraph_ranking:
  assumes "finite (Vs G)"

  assumes "M \<subseteq> G"
  shows "ranking' Y G M js \<subseteq> G"
  using assms
  by (induction js arbitrary: M)
     (auto dest: subgraph_step simp: ranking_Cons)

lemma subgraph_ranking':
  assumes "finite (Vs G)"

  assumes "M \<subseteq> G"
  assumes "e \<in> ranking' Y G M js"
  shows "e \<in> G"
  using assms
  by (auto dest: subgraph_ranking)

lemma bipartite_ranking:
  assumes "finite (Vs G)"

  assumes "bipartite G L R"
  assumes "M \<subseteq> G"
  shows "bipartite (ranking' Y G M js) L R"
  using assms
  by (auto dest: subgraph_ranking intro: bipartite_subgraph)

lemma edge_in_ranking:
  assumes "e \<in> ranking' Y G M js"
  shows "e \<in> M \<or> (\<exists>j \<in> set js. j \<in> e)"
  using assms
  by (induction js arbitrary: M)
     (auto dest: edge_in_step simp: ranking_Cons)

lemma edge_in_rankingE:
  assumes "e \<in> ranking' Y G M js"
  obtains "e \<in> M" | j where "j \<in> set js" "j \<in> e"
  using assms
  by (auto dest: edge_in_ranking)

lemma step_remove_unmatched_eq:
  assumes "bipartite G L R"
  assumes "finite (Vs G)"
  assumes "i \<in> L" "j \<in> R"
  assumes "i \<notin> Vs (step Y G M j)"
  assumes "inj_on Y L"
  shows "step Y (G \<setminus> {i}) M j = step Y G M j"
proof(cases "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G} \<noteq> {} \<and> j \<notin> Vs M")
  case False
  {
    assume "j \<in> Vs M"
    then have "step Y (G \<setminus> {i}) M j = step Y G M j"
      by (simp add: step_def)
  } note a = this

  {
    assume "j \<notin> Vs M"
    with False have *: "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G} = {}"
      by blast

    then have "{i'. i' \<notin> Vs M \<and> {i',j} \<in> (G \<setminus> {i})} = {}"
      using remove_vertices_subgraph' remove_vertices_subgraph_Vs
      by blast

    with * have "step Y (G \<setminus> {i}) M j = step Y G M j"
      by (simp add: step_def)
  }

  with a show ?thesis
    by blast
next
  case True
  let ?ns = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G}"
  and ?ns' = "{i'. i' \<notin> Vs M \<and> {i',j} \<in> G \<setminus> {i}}"

  from \<open>bipartite G L R\<close> \<open>j \<in> R\<close> have "?ns \<subseteq> L"
    by (auto dest: bipartite_edgeD)

  from assms have "finite ?ns"
    by blast

  have "?ns' \<subseteq> ?ns"
    using remove_vertices_subgraph_Vs remove_vertices_subgraph'
    by fast

  with \<open>?ns \<subseteq> L\<close> have "?ns' \<subseteq> L"
    by auto

  obtain i' where i': "arg_min_on Y ?ns = i'"
    by blast

  with True \<open>finite ?ns\<close> have "i' \<in> ?ns"
    by (auto dest: arg_min_if_finite)

  from i' \<open>finite ?ns\<close> have i'_least: "y \<in> ?ns \<Longrightarrow> Y i' \<le> Y y" for y
    by (auto intro: arg_min_least)

  from i' True have step_eq: "step Y G M j = insert {i',j} M"
    by (simp add: step_def)

  with assms have "i \<noteq> i'" "i \<noteq> j"
    by auto

  with \<open>i' \<in> ?ns\<close> have i'_ns': "i' \<in> ?ns'"
    by (auto intro: in_remove_verticesI)

  then have "?ns' \<noteq> {}"
    by blast

  have "arg_min_on Y ?ns' = i'"
    unfolding arg_min_on_def
    proof (intro arg_min_inj_eq, goal_cases)
      case 1
      from \<open>?ns' \<subseteq> L\<close> show ?case
        by (auto intro: inj_on_subset[OF \<open>inj_on Y L\<close>])
    next
      case 2
      from i'_ns' show ?case .
    next
      case 3
      from i'_least \<open>?ns' \<subseteq> ?ns\<close> show ?case
        by blast
    qed

    with True step_eq \<open>?ns' \<noteq> {}\<close> show ?thesis
      by (simp add: step_def)
qed

lemma ranking_remove_unmatched_eq:
  assumes "finite (Vs G)"
  assumes "bipartite G L R"
  assumes "i \<in> L" "set js \<subseteq> R"
  assumes "inj_on Y L"
  assumes "i \<notin> Vs (ranking' Y G M js)"
  shows "ranking' Y (G \<setminus> {i}) M js = ranking' Y G M js"
  using assms
proof (induction js arbitrary: M)
  case (Cons j js)

  from Cons.prems have "step Y (G \<setminus> {i}) M j = step Y G M j"
    by (intro step_remove_unmatched_eq)
       (auto dest: ranking_mono_vs simp: ranking_Cons)
  
  with Cons show ?case
    by (simp add: ranking_Cons)
qed simp

lemma dominance_matched:
  assumes "finite (Vs G)"
  assumes "bipartite G L R"
  assumes "set js = R"
  assumes "inj_on Y L"

  assumes "i \<in> L" "j \<in> R"
  assumes "{i,j} \<in> G"
  assumes "{i',j} \<in> ranking Y (G \<setminus> {i}) js"
  assumes "Y i < Y i'"
  shows "i \<in> Vs (ranking Y G js)"
proof -
  from \<open>set js = R\<close> \<open>j \<in> R\<close> obtain pre suff where js_split: "js = pre @ j # suff" "j \<notin> set pre"
    by (auto dest: split_list_first)

  from \<open>finite (Vs G)\<close> \<open>bipartite G L R\<close> have "bipartite (ranking Y (G \<setminus> {i}) js) L R"
    by (auto intro: bipartite_ranking finite_subset[OF _ \<open>finite (Vs G)\<close>]
        bipartite_subgraph[OF \<open>bipartite G L R\<close> remove_vertices_subgraph] dest: remove_vertices_subgraph_Vs')

  with \<open>{i',j} \<in> ranking Y (G \<setminus> {i}) js\<close> \<open>j \<in> R\<close> have "i' \<in> L"
    by (auto dest: bipartite_edgeD)

  have "bipartite (ranking Y (G \<setminus> {i}) pre) L R"
    by (intro bipartite_subgraph[OF \<open>bipartite (ranking Y (G \<setminus> {i}) js) L R\<close>])
       (auto simp: js_split ranking_append intro: ranking_mono)

  from \<open>finite (Vs G)\<close> have "matching (ranking Y (G \<setminus> {i}) js)"
    by (auto intro: matching_ranking finite_subset dest!: remove_vertices_subgraph_Vs')

  from \<open>i \<in> L\<close> \<open>i' \<in> L\<close> \<open>j \<in> R\<close> \<open>bipartite G L R\<close> have "i \<noteq> j" "i' \<noteq> j"
    by (auto dest: bipartite_disjointD)

  show ?thesis
  proof (cases "i \<in> Vs (ranking Y G pre)")
    case True
    with js_split show ?thesis
      by (auto simp only: ranking_append dest: ranking_mono_vs)
  next
    case False

    have "i' \<notin> Vs (ranking Y (G \<setminus> {i}) pre)"
    proof (rule ccontr, simp)
      assume "i' \<in> Vs (ranking Y (G \<setminus> {i}) pre)"
      then obtain e where e: "e \<in> ranking Y (G \<setminus> {i}) pre" "i' \<in> e"
        by (auto elim: vs_member_elim)

      from e js_split have "e \<in> ranking Y (G \<setminus> {i}) js"
        by (auto simp: ranking_append intro: ranking_mono)

      from e obtain j' where "j' \<in> e" "j' \<in> set pre"
        by (auto elim: edge_in_rankingE)

      with js_split \<open>set js = R\<close> have "j' \<in> R" "j' \<noteq> j"
        by auto

      with \<open>bipartite G L R\<close> \<open>i \<in> L\<close> \<open>i' \<in> L\<close> \<open>j \<in> R\<close> \<open>i' \<in> e\<close> \<open>j' \<in> e\<close> have "e \<noteq> {i',j}" "e \<inter> {i',j} \<noteq> {}"
        by (auto dest: bipartite_disjointD)

      with \<open>{i',j} \<in> ranking Y (G \<setminus> {i}) js\<close> \<open>e \<in> ranking Y (G \<setminus> {i}) js\<close>
      have "\<not>matching (ranking Y (G \<setminus> {i}) js)"
        unfolding matching_def
        by force

      with \<open>matching (ranking Y (G \<setminus> {i}) js)\<close> show False
        by blast
    qed

    from assms False js_split have "ranking Y (G \<setminus> {i}) pre = ranking Y G pre"
      by (intro ranking_remove_unmatched_eq) auto

    let ?ns = "{i. i \<notin> Vs (ranking Y G pre) \<and> {i,j} \<in> G}"
    let ?ns' = "{i'. i' \<notin> Vs (ranking Y (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}"

    note vs_member_intro[rule del]
    from False \<open>i \<noteq> j\<close> \<open>{i,j} \<in> G\<close> \<open>ranking Y (G \<setminus> {i}) pre = ranking Y G pre\<close>
    have *: "?ns  = insert i ?ns'"
      by (auto intro: in_remove_vertices_vsI in_remove_verticesI dest: edges_are_Vs remove_vertices_subgraph')

    have **: "i' = arg_min_on Y ?ns'"
    proof (rule ccontr)
      assume "i' \<noteq> arg_min_on Y ?ns'"

      then obtain i'' where i'': "arg_min_on Y ?ns' = i''" "i'' \<noteq> i'"
        by blast

      have "step Y (G \<setminus> {i}) (ranking Y (G \<setminus> {i}) pre) j = insert {i'',j} (ranking Y (G \<setminus> {i}) pre)"
      proof (intro step_insertI, goal_cases)
        case 1
        from \<open>{i',j} \<in> ranking Y (G \<setminus> {i}) js\<close> have "{i',j} \<in> G \<setminus> {i}"
          using finite_subset[OF remove_vertices_subgraph_Vs \<open>finite (Vs G)\<close>]
          by (auto intro: subgraph_ranking')

        with \<open>i' \<notin> Vs (ranking Y (G \<setminus> {i}) pre)\<close> show ?case
          by auto
      next
        case 2
        then show ?case
          by (smt (verit) Un_iff \<open>ranking Y (G \<setminus> {i}) pre = ranking Y G pre\<close> assms(1) assms(2) assms(3) assms(6) bipartite_eqI edge_in_ranking empty_iff js_split(1) js_split(2) set_append subgraph_ranking subset_eq vs_member)
      next
        case 3
        with i'' show ?case
          by blast
      qed

      with js_split have "{i'',j} \<in> ranking Y (G \<setminus> {i}) js"
        by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

      with \<open>{i',j} \<in> ranking Y (G \<setminus> {i}) js\<close> \<open>i'' \<noteq> i'\<close> \<open>i' \<noteq> j\<close> have "\<not>matching (ranking Y (G \<setminus> {i}) js)"
        unfolding matching_def
        by fast

      with \<open>matching (ranking Y (G \<setminus> {i}) js)\<close> show False
        by blast
    qed

    have "arg_min_on Y {i. i \<notin> Vs (ranking Y G pre) \<and> {i,j} \<in> G} = i"
      unfolding arg_min_on_def
    proof (intro arg_min_less_eq, goal_cases)
      case 1
      from False \<open>{i,j} \<in> G\<close> show ?case
        by (auto dest: edges_are_Vs)
    next
      case 2
      have "\<lbrakk>i'' \<notin> Vs (ranking Y (G \<setminus> {i}) pre);  {i'',j} \<in> G \<setminus> {i}\<rbrakk> \<Longrightarrow> Y i' \<le> Y i''" for i''
        unfolding **
      proof (intro arg_min_least, goal_cases)
        case 1
        from \<open>finite (Vs G)\<close> show ?case
          by (auto dest: finite_subset[OF remove_vertices_subgraph_Vs, of G "{i}"])
      qed blast+

      with \<open>Y i < Y i'\<close> show ?case
        unfolding *
        by fastforce
    qed

    then have "step Y G (ranking Y G pre) j = insert {i,j} (ranking Y G pre)"
      unfolding step_def
      apply (auto)
       apply (meson False assms(7) edges_are_Vs(1))
      by (smt (verit) Un_iff assms(1) assms(2) assms(3) bex_empty bipartite_eqI edge_in_ranking empty_subsetI in_mono insertI1 js_split(1) js_split(2) list.set(2) set_append subgraph_ranking vs_member)

    then show ?thesis
      by (auto simp: js_split ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  qed
qed

lemma dominance_unmatched:
  assumes "finite (Vs G)"
  assumes "bipartite G L R"
  assumes "inj_on Y L"

  assumes "i \<in> L"
  assumes "j \<in> set js"
  assumes "set js \<subseteq> R"

  assumes "{i,j} \<in> G"
  assumes "j \<notin> Vs (ranking Y (G \<setminus> {i}) js)"
  shows "i \<in> Vs (ranking Y G js)"
proof -
  from \<open>j \<in> set js\<close> obtain pre suff where js_split: "js = pre @ j # suff"
    by (auto dest: split_list)

  from \<open>j \<in> set js\<close> \<open>set js \<subseteq> R\<close> have "j \<in> R"
    by blast

  with \<open>i \<in> L\<close> \<open>bipartite G L R\<close> have "i \<noteq> j"
    by (auto dest: bipartite_disjointD)

  from js_split \<open>j \<notin> Vs (ranking Y (G \<setminus> {i}) js)\<close> have j_not_pre:  "j \<notin> Vs (ranking Y (G \<setminus> {i}) pre)"
    by (auto simp: ranking_append dest: ranking_mono_vs)


  show ?thesis
  proof (cases "i \<in> Vs (ranking Y G pre)")
    case True
    with js_split show ?thesis
      by (auto simp: ranking_append dest: ranking_mono_vs)
  next
    case False
    note i_not_pre = this

    with assms js_split have pre_eq: "ranking Y (G \<setminus> {i}) pre = ranking Y G pre"
      by (intro ranking_remove_unmatched_eq) auto

    have "step Y G (ranking Y G pre) j = insert {i,j} (ranking Y G pre)"
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
      proof (cases "{i'. i' \<notin> Vs (ranking Y (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}} = {}")
        case True
        with False \<open>{i,j} \<in> G\<close> have "{i. i \<notin> Vs (ranking Y G pre) \<and> {i,j} \<in> G} = {i}"
          apply (auto simp: pre_eq)
          by (metis \<open>i \<noteq> j\<close> disjoint_insert(1) empty_iff in_remove_verticesI inf_bot_right insert_iff)

        then show ?thesis
          unfolding arg_min_on_def
          by (auto intro: arg_min_less_eq[symmetric])
      next
        case False
        show ?thesis
        proof (rule ccontr)
          let ?ns = "{i. i \<notin> Vs (ranking Y G pre) \<and> {i,j} \<in> G}"
          and ?ns' = "{i'. i' \<notin> Vs (ranking Y (G \<setminus> {i}) pre) \<and> {i',j} \<in> G \<setminus> {i}}"
          let ?i' = "arg_min_on Y ?ns"

          assume "i \<noteq> ?i'"

          from i_not_pre \<open>{i,j} \<in> G\<close> \<open>finite (Vs G)\<close> have "?i' \<in> ?ns"
          by (intro arg_min_if_finite) auto

        have arg_min': "arg_min_on Y ?ns' = ?i'"
        proof (subst arg_min_on_def, intro arg_min_inj_eq, goal_cases)
          case 1
          have "?ns' \<subseteq> ?ns"
            by (auto simp: pre_eq dest: remove_vertices_subgraph')

          also from \<open>bipartite G L R\<close> \<open>j \<in> R\<close> have "\<dots> \<subseteq> L"
            by (auto dest: bipartite_edgeD)

          finally have "?ns' \<subseteq> L" .

          with \<open>inj_on Y L\<close> show ?case
            by (auto intro: inj_on_subset)
        next
          case 2
          from \<open>?i' \<in> ?ns\<close> \<open>i \<noteq> ?i'\<close> \<open>i \<noteq> j\<close> show ?case
            by (auto simp: pre_eq intro: in_remove_verticesI)
        next
          case 3
          from False \<open>finite (Vs G)\<close> \<open>{i,j} \<in> G\<close> show ?case
            by (auto simp: pre_eq intro: arg_min_least dest: remove_vertices_subgraph')
        qed

        with False j_not_pre have "step Y (G \<setminus> {i}) (ranking Y (G \<setminus> {i}) pre) j = insert {?i',j} (ranking Y (G \<setminus> {i}) pre)"
          by (intro step_insertI) auto

        with js_split have "j \<in> Vs (ranking Y (G \<setminus> {i}) js)"
          by (auto simp: ranking_append ranking_Cons intro: ranking_mono)

        with \<open>j \<notin> Vs (ranking Y (G \<setminus> {i}) js)\<close> show False
          by blast
      qed
    qed
  qed

  with js_split show ?thesis
    by (auto simp: ranking_append ranking_Cons intro: ranking_mono)
  qed
qed

definition y\<^sub>c :: "('a \<Rightarrow> 'b::{linorder,one}) \<Rightarrow> 'a graph \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  "y\<^sub>c Y G js i j \<equiv> 
    if j \<in> Vs (ranking Y (G \<setminus> {i}) js)
    then Y (THE i'. {i',j} \<in> ranking Y (G \<setminus> {i}) js)
    else 1"

lemma dominance:
  assumes "finite (Vs G)"
  assumes "bipartite G L R"
  assumes "inj_on Y L"

  assumes "i \<in> L"
  assumes "j \<in> set js"
  assumes "set js = R"
  assumes "{i,j} \<in> G"

  assumes "Y i < y\<^sub>c Y G js i j"
  shows "i \<in> Vs (ranking Y G js)"
proof (cases "j \<in> Vs (ranking Y (G \<setminus> {i}) js)")
  case True
  then obtain e where e: "e \<in> ranking Y (G \<setminus> {i}) js" "j \<in> e"
    by (auto elim: vs_member_elim)

  from \<open>finite (Vs G)\<close> \<open>bipartite G L R\<close> have "bipartite (ranking Y (G \<setminus> {i}) js) L R"
    by (intro bipartite_ranking bipartite_remove_vertices) blast+

  with e \<open>j \<in> set js\<close> \<open>set js = R\<close> obtain i' where i': "{i',j} \<in> ranking Y (G \<setminus> {i}) js"
    by (smt (verit) bipartite_disjointD bipartite_edgeE disjoint_iff empty_iff insert_iff)

  from \<open>finite (Vs G)\<close> have "matching (ranking Y (G \<setminus> {i}) js)"
    by (auto intro: matching_ranking)

  with i' have the_i': "(THE i'. {i',j} \<in> ranking Y (G \<setminus> {i}) js) = i'"
    by (auto dest: the_match)

  show ?thesis
  proof (intro dominance_matched, goal_cases)
    from True \<open>Y i < y\<^sub>c Y G js i j\<close> show "Y i < Y i'"
      by (simp add: y\<^sub>c_def the_i')
  qed (use assms i' in simp_all)
next
  case False
  with assms show ?thesis
    by (auto intro: dominance_unmatched)
qed

context
  fixes L :: "'a set" and R :: "'a set"
  fixes G :: "'a graph"
  fixes Y :: "'a \<Rightarrow> real"

  assumes fin_L: "finite L" and fin_R: "finite R"
  assumes bipartite: "bipartite G L R"
  assumes parts_minimal: "Vs G = L \<union> R"

  assumes Y_funcset: "Y \<in> L \<rightarrow> {0..1}"
  assumes inj_Y: "inj_on Y L"

  fixes g :: "real \<Rightarrow> real"
  fixes F :: "real"
  
  assumes g_funcset: "g \<in> {0..1} \<rightarrow> {0..1}"
  assumes g_mono: "mono_on g {0..1}"
  assumes g_One: "g 1 = 1"

  assumes F_neq_0: "F \<noteq> 0"
begin

definition "n \<equiv> card (Vs G)"
definition "m \<equiv> card G"

definition Vs_enum :: "'a \<Rightarrow> nat" where
  "Vs_enum x \<equiv> if x \<in> L then to_nat_on L x else to_nat_on R x + card L"

definition Vs_enum_inv :: "nat \<Rightarrow> 'a" where
  "Vs_enum_inv i \<equiv> if i < card L then from_nat_into L i else from_nat_into R (i - card L)"

interpretation graph_abs_G: graph_abs G
  using bipartite fin_L fin_R
  by (intro finite_parts_bipartite_graph_abs)

abbreviation G_enum :: "'a set \<Rightarrow> nat" where
  "G_enum \<equiv> to_nat_on G"

definition incidence_matrix :: "nat mat" where
  "incidence_matrix \<equiv> mat n m (\<lambda>(i,j). of_bool ({Vs_enum_inv i, Vs_enum_inv j} \<in> G))"

fun step_primal_dual :: "('a graph \<times> nat vec \<times> real vec) \<Rightarrow> 'a \<Rightarrow> ('a graph \<times> nat vec \<times> real vec)" where
  "step_primal_dual (M,p,d) j = (
    let ns = {i. i \<notin> Vs M \<and> {i,j} \<in> G} in
    if ns \<noteq> {} \<and> j \<notin> Vs M
    then let i = arg_min_on Y ns in (
      insert {i,j} M,
      p |\<^sub>v G_enum {i,j} \<mapsto> 1,
      d |\<^sub>v Vs_enum i \<mapsto> g (Y i) / F |\<^sub>v Vs_enum j \<mapsto> (1 - g (Y i)) / F
    )
    else (M,p,d)
  )"

declare step_primal_dual.simps[simp del]

lemma step_primal_dual_no_neighbor[simp]: "{i. i \<notin> Vs M \<and> {i,j} \<in> G} = {} \<Longrightarrow> step_primal_dual (M,p,d) j = (M,p,d)"
  by (simp add: step_primal_dual.simps)

lemma step_primal_dual_j_matched[simp]: "j \<in> Vs M \<Longrightarrow> step_primal_dual (M,p,d) j = (M,p,d)"
  by (simp add: step_primal_dual.simps)

lemma step_primal_dual_new_match[simp]:
  fixes M j
  defines "ns \<equiv> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"
  assumes "ns \<noteq> {}" "j \<notin> Vs M"
  shows "step_primal_dual (M,p,d) j = (
    insert {arg_min_on Y ns, j} M,
    p |\<^sub>v G_enum {arg_min_on Y ns, j} \<mapsto> 1,
    d |\<^sub>v Vs_enum (arg_min_on Y ns) \<mapsto> (g \<circ> Y) (arg_min_on Y ns) / F |\<^sub>v Vs_enum j \<mapsto> (1 - ((g \<circ> Y) (arg_min_on Y ns))) / F
  )"
  using assms
  by (simp add: step_primal_dual.simps Let_def)

definition "ranking_primal_dual' M \<equiv> foldl step_primal_dual M"
abbreviation "ranking_primal_dual \<equiv> ranking_primal_dual' ({}, 0\<^sub>v m, 0\<^sub>v n)"

lemma ranking_primal_dual_Nil[simp]: "ranking_primal_dual' M [] = M"
  unfolding ranking_primal_dual'_def
  by simp

lemma ranking_primal_dual_Cons: "ranking_primal_dual' M (j#js) = ranking_primal_dual' (step_primal_dual M j) js"
  unfolding ranking_primal_dual'_def
  by simp

definition primal_sol :: "'a graph \<Rightarrow> nat vec" where
  "primal_sol M \<equiv> vec m (\<lambda>i. of_bool (from_nat_into G i \<in> M))"

definition dual_sol :: "'a graph \<Rightarrow> real vec" where
  "dual_sol M \<equiv> vec n (\<lambda>i.
    if Vs_enum_inv i \<in> Vs M
    then
      if i < card L then (g \<circ> Y) (Vs_enum_inv i) / F
      else (1 - (g \<circ> Y) (THE l. {l, Vs_enum_inv i} \<in> M)) / F
    else 0
  )"

lemma dim_primal_sol[simp]: "dim_vec (primal_sol M) = m"
  by (simp add: primal_sol_def)

lemma dim_dual_sol[simp]: "dim_vec (dual_sol M) = n"
  by (simp add: dual_sol_def)

lemma "e \<in> G \<Longrightarrow> primal_sol M $ (G_enum e) = 1 \<longleftrightarrow> e \<in> M"
  unfolding primal_sol_def
  by (auto simp add: countable_finite graph_abs_G.finite_E to_nat_on_less_card m_def)

lemma n_sum: "n = card L + card R"
  using bipartite parts_minimal fin_L fin_R
  by (auto dest: bipartite_disjointD simp: card_Un_disjoint n_def)

lemma geq_L_less_n_less_R: "card L \<le> i \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto simp: n_sum)

lemma geq_L_less_n_less_R': "\<not> i < card L \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto intro: geq_L_less_n_less_R)

lemma Vs_cases: 
  assumes "x \<in> Vs G"
  obtains "x \<in> L \<and> x \<notin> R" | "x \<in> R \<and> x \<notin> L"
  using assms parts_minimal bipartite
  by (auto dest: bipartite_disjointD)

lemma i_cases:
  assumes "i < n"
  obtains "i < card L" | "card L \<le> i" "i < card L + card R"
  using assms
  by (auto simp: n_sum) linarith

lemma
  shows L_inv_enum[simp]: "l \<in> L \<Longrightarrow> from_nat_into L (to_nat_on L l) = l"
    and L_enum_inv[simp]: "i < card L \<Longrightarrow> to_nat_on L (from_nat_into L i) = i"
    and R_inv_enum[simp]: "r \<in> R \<Longrightarrow> from_nat_into R (to_nat_on R r) = r"
    and R_enum_inv[simp]: "j < card R \<Longrightarrow> to_nat_on R (from_nat_into R j) = j"
  using fin_L fin_R
  by (auto simp: countable_finite intro: to_nat_on_from_nat_into_less)

lemma
  shows L_enum_less_card: "l \<in> L \<Longrightarrow> to_nat_on L l < card L"
    and R_enum_less_card: "r \<in> R \<Longrightarrow> to_nat_on R r < card R"
  using fin_L fin_R
  by (auto intro: to_nat_on_less_card)

lemma
  shows L_enum_less_n: "l \<in> L \<Longrightarrow> to_nat_on L l < n"
    and R_enum_less_n: "r \<in> R \<Longrightarrow> to_nat_on R r + card L < n"
  by (auto simp: n_sum dest: L_enum_less_card R_enum_less_card)


lemma
  shows [simp]: "l \<in> L \<Longrightarrow> Vs_enum l = to_nat_on L l"
    and [simp]: "i < card L \<Longrightarrow> Vs_enum_inv i = from_nat_into L i"
  unfolding Vs_enum_def Vs_enum_inv_def
  by auto

lemma
  shows [simp]: "r \<in> R \<Longrightarrow> Vs_enum r = to_nat_on R r + card L"
    and [simp]: "card L \<le> i \<Longrightarrow> Vs_enum_inv i = from_nat_into R (i - card L)"
  using bipartite
  unfolding Vs_enum_def Vs_enum_inv_def
  by (auto dest: bipartite_disjointD)

lemma
  shows Vs_inv_enum[simp]: "x \<in> Vs G \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
    and Vs_enum_inv[simp]: "i < n \<Longrightarrow> Vs_enum (Vs_enum_inv i) = i"
  using fin_L fin_R
   apply (auto elim!: Vs_cases simp: Vs_enum_inv_def Vs_enum_def n_sum dest: L_enum_less_card intro!: from_nat_into)
  by (metis Un_iff Vs_cases add.right_neutral card.empty from_nat_into parts_minimal)

lemma bij_betw_Vs_enum: 
  shows "bij_betw Vs_enum (Vs G) {0..<n}"
  by (intro bij_betwI[where g = "Vs_enum_inv"])
     (auto simp: Vs_inv_enum Vs_enum_inv parts_minimal elim!: Vs_cases i_cases intro!: L_enum_less_n R_enum_less_n from_nat_into)

lemma fst_step_primal_dual: "fst (step_primal_dual (M,p,d) j) = step Y G M j"
  by (auto simp: step_def Let_def)

lemma fst_ranking_primal_dual': "fst acc = M \<Longrightarrow> fst (ranking_primal_dual' acc js) = ranking' Y G M js"
  by (induction js arbitrary: acc M)
     (auto simp: ranking_primal_dual_Cons ranking_Cons fst_step_primal_dual)

lemma fst_ranking_primal_dual: "fst (ranking_primal_dual' (M,p,d) js) = ranking' Y G M js"
  by (auto intro!: fst_ranking_primal_dual')

lemma Vs_enum_neqI: "v \<in> Vs G \<Longrightarrow> v' \<in> Vs G \<Longrightarrow> v \<noteq> v' \<Longrightarrow> Vs_enum v \<noteq> Vs_enum v'"
  by (metis Vs_inv_enum)

lemma G_enum_neqI: "e \<in> G \<Longrightarrow> e' \<in> G \<Longrightarrow> e \<noteq> e' \<Longrightarrow> G_enum e \<noteq> G_enum e'"
  by (simp add: countable_finite graph_abs_G.finite_E)

lemma primal_dot_One_card: "M \<subseteq> G \<Longrightarrow> primal_sol M \<bullet> (1\<^sub>v m) = card M"
  apply (auto simp: scalar_prod_def m_def primal_sol_def)
  apply (intro bij_betw_same_card[where f = "from_nat_into G"] bij_betwI[where g = G_enum])
     apply (auto intro!: to_nat_on_less_card to_nat_on_from_nat_into_less simp: countable_finite graph_abs_G.finite_E in_mono)
  done

lemma dual_dot_One_card:
  assumes "M \<subseteq> G"
  assumes "matching M"
  shows "dual_sol M \<bullet> (1\<^sub>v n) = card M / F"
proof -
  from graph_abs_G.graph have "dual_sol M \<bullet> (1\<^sub>v n) = 
    (\<Sum>i\<in>{0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> {i. i < card L}. g (Y (Vs_enum_inv i)) / F) +
    (\<Sum>i\<in>{0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> - {i. i < card L}. (1 - g (Y (THE l. {l, Vs_enum_inv i} \<in> M))) / F)"
    by (simp add: dual_sol_def scalar_prod_def sum.If_cases)

  have L_sum_matching: "(\<Sum>i\<in>{0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> {i. i < card L}. g (Y (Vs_enum_inv i)) / F) =
    (\<Sum>e\<in>M. g (Y (THE l. l \<in> L \<and> l \<in> e)) / F)"
  proof (rule sum.reindex_bij_witness[where j = "\<lambda>i. (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e)" and
          i = "\<lambda>e. Vs_enum (THE l. l \<in> L \<and> l \<in> e)"])
    fix i
    assume i: "i \<in> {0..<local.n} \<inter> {i. local.Vs_enum_inv i \<in> Vs M} \<inter> {i. i < card L}"
    then obtain e where e: "e \<in> M" "Vs_enum_inv i \<in> e" and i_less_n: "i < n"
      by (auto elim: vs_member_elim)

    with \<open>matching M\<close> have the_e: "(THE e. e \<in> M \<and> Vs_enum_inv i \<in> e) = e"
      by (auto intro!: the_equality dest: matching_unique_match)

    with e show "(THE e. e \<in> M \<and> local.Vs_enum_inv i \<in> e) \<in> M"
      by blast

    from bipartite e obtain l r where e': "e = {l,r}" "l \<in> L" "r \<in> R"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    from i have "Vs_enum_inv i \<in> L"
      by (auto intro: from_nat_into)

    with bipartite e e' have the_l: "(THE l. l \<in> L \<and> l \<in> e) = Vs_enum_inv i"
      by (auto dest: bipartite_disjointD)

    with i_less_n show "Vs_enum (THE l. l \<in> L \<and> l \<in> (THE e. e \<in> M \<and> local.Vs_enum_inv i \<in> e)) = i"
      by (auto simp: the_e the_l)

    show "g (Y (THE l. l \<in> L \<and> l \<in> (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e))) / F = g (Y (Vs_enum_inv i)) / F"
      by (simp add: the_e the_l)
  next
    fix e
    assume eM: "e \<in> M"

    with bipartite obtain l r where e: "e = {l,r}" "l \<in> L" "r \<in> R"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    with bipartite have the_l: "(THE l. l \<in> L \<and> l \<in> e) = l"
      by (auto dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>] bipartite_disjointD)

    from eM e \<open>matching M\<close> have the_e: "(THE e. e \<in> M \<and> l \<in> e) = e"
      apply (intro the_equality)
       apply simp
      by (meson insertCI matching_unique_match)

    from parts_minimal \<open>l \<in> L\<close> have "l \<in> Vs G"
      by blast

    then show "(THE e'. e' \<in> M \<and> Vs_enum_inv (Vs_enum (THE l. l \<in> L \<and> l \<in> e)) \<in> e') = e"
      by (simp add: the_l Vs_inv_enum the_e)

    from \<open>l \<in> L\<close> show "Vs_enum (THE l. l \<in> L \<and> l \<in> e) \<in> {0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> {i. i < card L}"
      apply (auto simp: the_l intro: L_enum_less_n L_enum_less_card)
      apply (metis L_inv_enum Vs_enum_inv_def e(1) eM edges_are_Vs(1) fin_L to_nat_on_less_card)
      done
  qed

  have R_sum_matching: "(\<Sum>i\<in>{0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> - {i. i < card L}. (1 - g (Y (THE l. {l, Vs_enum_inv i} \<in> M))) / F) =
   (\<Sum>e\<in>M. (1 - g (Y (THE l. l \<in> L \<and> l \<in> e))) / F)"
  proof (rule sum.reindex_bij_witness[where j = "\<lambda>i. (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e)" and
        i = "\<lambda>e. Vs_enum (THE r. r \<in> R \<and> r \<in> e)"])
    fix i
    assume i: "i \<in> {0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> - {i. i < card L}"

    then obtain e where e: "e \<in> M" "Vs_enum_inv i \<in> e" and i_less_n: "i < n"
      by (auto elim: vs_member_elim)

    with \<open>matching M\<close> have the_e: "(THE e. e \<in> M \<and> Vs_enum_inv i \<in> e) = e"
      by (auto intro!: the_equality dest: matching_unique_match)

    with e show "(THE e. e \<in> M \<and> Vs_enum_inv i \<in> e) \<in> M"
      by blast

    from bipartite e obtain l r where e': "e = {l,r}" "l \<in> L" "r \<in> R"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    with i have "Vs_enum_inv i \<in> R"
      by (auto intro: from_nat_into)

    with e' e parts_minimal have the_r: "(THE r. r \<in> R \<and> r \<in> e) = Vs_enum_inv i"
      by (auto elim: Vs_cases)

    from i_less_n show "Vs_enum (THE r. r \<in> R \<and> r \<in> (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e)) = i"
      by (simp add: the_e the_r)

    from e e' bipartite have the_l: "(THE l. l \<in> L \<and> l \<in> e) = l"
      by (intro the_equality)
         (auto dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>] bipartite_disjointD)

    from e e' \<open>matching M\<close> have the_l': "(THE l. {l, local.Vs_enum_inv i} \<in> M) = l"
      apply (intro the_equality)
      using Vs_cases \<open>local.Vs_enum_inv i \<in> R\<close> assms(1) empty_iff apply blast
      by (metis (no_types, lifting) Vs_cases \<open>local.Vs_enum_inv i \<in> R\<close> assms(1) edges_are_Vs(1) insertE singleton_iff subset_eq the_match)

    show "(1 - g (Y (THE l. l \<in> L \<and> l \<in> (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e)))) / F = (1 - g (Y (THE l. {l, Vs_enum_inv i} \<in> M))) / F"
      by (simp add: the_e the_l the_l')
  next
    fix e
    assume eM: "e \<in> M"

    with bipartite obtain l r where e: "e = {l,r}" "l \<in> L" "r \<in> R" "l \<noteq> r"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    with bipartite have the_r: "(THE r. r \<in> R \<and> r \<in> e) = r"
      by (intro the_equality)
         (auto dest: bipartite_disjointD)

    from eM \<open>e = {l,r}\<close> \<open>matching M\<close> have the_e: "(THE e. e \<in> M \<and> r \<in> e) = e"
      by (intro the_equality matching_unique_match)
         auto

    from \<open>r \<in> R\<close> have r_inv_enum: "Vs_enum_inv (Vs_enum r) = r"
      by simp

    then show "(THE e'. e' \<in> M \<and> Vs_enum_inv (Vs_enum (THE r. r \<in> R \<and> r \<in> e)) \<in> e') = e"
      by (simp add: the_r the_e)

    show "Vs_enum (THE r. r \<in> R \<and> r \<in> e) \<in> {0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> - {i. i < card L}"
      apply (simp add: the_r r_inv_enum)
      apply (intro conjI)
      using L_enum_less_n R_enum_less_n Vs_enum_def e(3) apply presburger
       apply (metis e(1) eM edges_are_Vs(2))
      by (simp add: e(3))
  qed

  with graph_abs_G.graph L_sum_matching show ?thesis
    by (auto simp: scalar_prod_def dual_sol_def n_def sum.If_cases simp flip: sum.distrib add_divide_distrib)
qed

lemma primal_is_dual_times_F:
  assumes "M \<subseteq> G"
  assumes "matching M"
  shows "primal_sol M \<bullet> (1\<^sub>v m) = dual_sol M \<bullet> (1\<^sub>v n) * F"
  using assms F_neq_0
  by (auto simp: primal_dot_One_card dual_dot_One_card)

lemma step_primal_dual_cases[case_names no_neighbor j_matched new_match]:
  fixes M j
  defines "ns \<equiv> {i. i \<notin> Vs M \<and> {i,j} \<in> G}"

  assumes "ns = {} \<Longrightarrow> P"
  assumes "j \<in> Vs M \<Longrightarrow> P"
  assumes "ns \<noteq> {} \<Longrightarrow> j \<notin> Vs M \<Longrightarrow> arg_min_on Y ns \<in> ns \<Longrightarrow> P"

  shows P
  using step_cases[of M j G]
proof cases
  case new_match
  with graph_abs_G.graph have "arg_min_on Y ns \<in> ns"
    unfolding ns_def
    by (intro arg_min_if_finite finite_unmatched_neighbors) auto
    
  with assms new_match show ?thesis
    by blast
qed (use assms in blast)+

lemma dim_vec_step_primal[simp]: "dim_vec ((fst \<circ> snd) (step_primal_dual (M,p,d) j)) = dim_vec p"
  using step_primal_dual_cases[of M j]
  by cases simp_all

lemma dim_vec_step_dual[simp]: "dim_vec ((snd \<circ> snd) (step_primal_dual (M,p,d) j)) = dim_vec d"
  using step_primal_dual_cases[of M j]
  by cases simp_all

lemmas dim_vec_step_primal_dual[simp] = dim_vec_step_primal[simplified] dim_vec_step_dual[simplified]

lemma dim_vec_ranking_primal[simp]: "dim_vec ((fst \<circ> snd) (ranking_primal_dual' (M,p,d) js)) = dim_vec p"
proof (induction js arbitrary: M p d)
  case (Cons j js)
  let ?step = "step_primal_dual (M,p,d) j"

  have "dim_vec ((fst \<circ> snd) (ranking_primal_dual' (fst ?step, (fst \<circ> snd) ?step, (snd \<circ> snd) ?step) js)) =
    dim_vec ((fst \<circ> snd) ?step)"
    by (intro Cons.IH)

  also have "\<dots> = dim_vec p" by simp

  finally show ?case
    by (simp add: ranking_primal_dual_Cons)
qed simp

lemma dim_vec_ranking_dual[simp]: "dim_vec ((snd \<circ> snd) (ranking_primal_dual' (M,p,d) js)) = dim_vec d"
proof (induction js arbitrary: M p d)
  case (Cons j js)
  let ?step = "step_primal_dual (M,p,d) j"

  have "dim_vec ((snd \<circ> snd) (ranking_primal_dual' (fst ?step, (fst \<circ> snd) ?step, (snd \<circ> snd) ?step) js)) =
    dim_vec ((snd \<circ> snd) ?step)"
    by (intro Cons.IH)

  also have "\<dots> = dim_vec d" by simp

  finally show ?case
    by (simp add: ranking_primal_dual_Cons)
qed simp

lemmas dim_vec_ranking_primal_dual[simp] = dim_vec_ranking_primal[simplified] dim_vec_ranking_dual[simplified]

lemma
  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  shows dim_vec_ranking_primal'[simp]: "dim_vec p = dim_vec p'"
    and dim_vec_ranking_dual'[simp]: "dim_vec d = dim_vec d'"
  using assms
  by (metis dim_vec_ranking_primal_dual fst_conv snd_conv)+

lemma step_primal_unmatched:
  assumes "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "e \<in> G"
  assumes "e \<notin> M"
  shows "p $ G_enum e = p' $ G_enum e"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match have "{?i,j} \<in> G"
    by blast

  from new_match have step: "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1,
    d' |\<^sub>v Vs_enum ?i \<mapsto> (g \<circ> Y) ?i / F |\<^sub>v Vs_enum j \<mapsto> (1 - (g \<circ> Y) ?i) / F
  )"
    by simp

  with assms have "e \<noteq> {?i,j}" and p: "p = p' |\<^sub>v G_enum {?i,j} \<mapsto> 1"
    by auto

  with \<open>e \<in> G\<close> \<open>{?i,j} \<in> G\<close> have "G_enum e \<noteq> G_enum {?i,j}"
    by (intro G_enum_neqI) auto

  with assms p show ?thesis
    by simp
qed (use assms in simp_all)

lemma ranking_primal_unmatched:
  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  assumes "e \<in> G"
  assumes "e \<notin> M"
  shows "p $ G_enum e = p' $ G_enum e"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  from Cons.prems have "p $ G_enum e = (fst \<circ> snd) ?step $ G_enum e"
    by (intro Cons.IH[where M' = "fst ?step" and d' = "(snd \<circ> snd) ?step"])
       (simp_all add: ranking_primal_dual_Cons)

  also from Cons.prems have "\<dots> = p' $ G_enum e"
  proof (intro step_primal_unmatched[where M' = M' and d' = d' and j = j and M = "fst ?step" and d = "(snd \<circ> snd) ?step"])
    have "fst (ranking_primal_dual' (M',p',d') (j#js)) = ranking' Y G M' (j#js)"
      by (simp add: fst_ranking_primal_dual)

    with Cons.prems show "e \<notin> fst ?step"
      by (auto simp: fst_step_primal_dual ranking_Cons dest: ranking_mono)
  qed simp_all

  finally show ?case .
qed simp

lemma step_primal_matched_previously:
  assumes "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "e \<in> M'"
  assumes "e \<in> G"
  shows "p $ G_enum e = p' $ G_enum e"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match \<open>e \<in> M'\<close> have "e \<noteq> {?i,j}" "{?i,j} \<in> G"
    by blast+

  with \<open>e \<in> G\<close> have "G_enum e \<noteq> G_enum {?i,j}"
    by (intro G_enum_neqI) auto

  from new_match have "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1,
    d' |\<^sub>v Vs_enum ?i \<mapsto> (g \<circ> Y) ?i / F |\<^sub>v Vs_enum j \<mapsto> (1 - (g \<circ> Y) ?i) / F
  )"
    by simp

  with \<open>G_enum e \<noteq> G_enum {?i,j}\<close> assms show ?thesis
    by auto
qed (use assms in simp_all)

lemma ranking_primal_matched_previously:
  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  assumes "e \<in> M'"
  assumes "e \<in> G"
  shows "p $ G_enum e = p' $ G_enum e"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  from Cons.prems have "p $ G_enum e = (fst \<circ> snd) ?step $ G_enum e"
  proof (intro Cons.IH[where M' = "fst ?step" and  d' = "(snd \<circ> snd) ?step"], goal_cases)
    case 2
    then show ?case
      by (simp add: fst_step_primal_dual step_mono)
  qed (simp_all add: ranking_primal_dual_Cons)

  also from Cons.prems have "\<dots> = p' $ G_enum e"
    by (intro step_primal_matched_previously[where M' = M' and d' = d' and j = j and M = "fst ?step" and d = "(snd \<circ> snd) ?step"])
       auto

  finally show ?case .
qed simp

lemma step_primal_matched:
  assumes "dim_vec p' = m"

  assumes "step_primal_dual (M',p',d') j = (M,p,d)"

  assumes "e \<notin> M'"
  assumes "e \<in> M"
  shows "p $ G_enum e = 1"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match have step: "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1,
    d' |\<^sub>v Vs_enum ?i \<mapsto> (g \<circ> Y) ?i / F |\<^sub>v Vs_enum j \<mapsto> (1 - (g \<circ> Y) ?i) / F
  )"
    by simp

  with assms new_match have "e = {?i,j}" "{?i,j} \<in> G"
    by auto

  with graph_abs_G.finite_E have "G_enum e = G_enum {?i,j}" "G_enum {?i,j} < m"
    by (auto simp: m_def intro: to_nat_on_less_card)

  with step assms \<open>e = {?i,j}\<close> show ?thesis
    by simp
qed (use assms in simp_all)

lemma ranking_primal_matched:
  assumes "dim_vec p' = m"

  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"

  assumes "e \<notin> M'"
  assumes "e \<in> M"
  shows "p $ G_enum e = 1"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  show ?case
  proof (cases "e \<in> fst ?step")
    case True

    with Cons.prems have "p $ G_enum e = (fst \<circ> snd) ?step $ G_enum e"
    proof (intro ranking_primal_matched_previously[where M' = "fst ?step" and d' = "(snd \<circ> snd) ?step" and js = js and M = M and d = d], goal_cases)
      case 3
      with graph_abs_G.graph show ?case
        by (auto simp: fst_step_primal_dual intro: step_matches_graph_edge)
    qed (simp_all add: ranking_primal_dual_Cons)

    also from True Cons.prems have "\<dots> = 1"
      by (intro step_primal_matched[where p' = p' and M' = M' and d' = d' and j = j and M = "fst ?step" and d = "(snd \<circ> snd) ?step"])
         auto

    finally show ?thesis
      .
  next
    case False
    with Cons.prems show ?thesis
      by (intro Cons.IH[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step" and d' = "(snd \<circ> snd) ?step"])
         (auto simp: ranking_primal_dual_Cons)
  qed
qed simp

lemma step_dual_unmatched:
  assumes "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "v \<in> Vs G"
  assumes "v \<notin> Vs M"
  shows "d $ Vs_enum v = d' $ Vs_enum v"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match have "j \<in> Vs G"
    by auto

  from new_match have step: "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1, 
    d' |\<^sub>v Vs_enum ?i \<mapsto> g (Y ?i) / F |\<^sub>v Vs_enum j \<mapsto> (1-g (Y ?i)) / F
  )"
    by simp

  with assms have "{?i,j} \<in> M" and d: "d = d' |\<^sub>v Vs_enum ?i \<mapsto> g (Y ?i) / F |\<^sub>v Vs_enum j \<mapsto> (1-g (Y ?i)) / F"
    by auto

  with \<open>v \<notin> Vs M\<close> have "?i \<noteq> v" "j \<noteq> v"
    by auto

  with \<open>?i \<in> ?ns\<close> \<open>v \<in> Vs G\<close> have *: "Vs_enum ?i \<noteq> Vs_enum v"
    by (intro Vs_enum_neqI) auto

  from \<open>j \<noteq> v\<close> \<open>j \<in> Vs G\<close> \<open>v \<in> Vs G\<close> have "Vs_enum j \<noteq> Vs_enum v"
    by (intro Vs_enum_neqI)

  with d * show ?thesis
    by auto
qed (use assms in simp_all)

lemma ranking_dual_unmatched:
  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  assumes "v \<in> Vs G"
  assumes "v \<notin> Vs M"
  shows "d $ Vs_enum v = d' $ Vs_enum v"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  from Cons have "d $ local.Vs_enum v = (snd \<circ> snd) ?step $ local.Vs_enum v"
    by (intro Cons.IH[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step"])
       (simp_all add: ranking_primal_dual_Cons)

  also from Cons.prems have "\<dots> = d' $ Vs_enum v"
  proof (intro step_dual_unmatched[where M' = M' and p' = p' and M = "fst ?step" and p = "(fst \<circ> snd) ?step"])
    have "fst (ranking_primal_dual' (M',p',d') (j#js)) = ranking' Y G M' (j#js)"
      by (simp add: fst_ranking_primal_dual)

    with Cons.prems show "v \<notin> Vs (fst ?step)"
      by (auto simp: fst_step_primal_dual ranking_Cons dest: ranking_mono_vs)
  qed simp_all

  finally show ?case .
qed simp

lemma step_dual_matched_previously:
  assumes "step_primal_dual (M',p',d') j = (M,p,d)"

  assumes "v \<in> Vs M'"
  assumes "v \<in> Vs G"

  shows "d $ Vs_enum v = d' $ Vs_enum v"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match have step: "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1,
    d' |\<^sub>v Vs_enum ?i \<mapsto> (g \<circ> Y) ?i / F |\<^sub>v Vs_enum j \<mapsto> (1 - (g \<circ> Y) ?i) / F
  )"
    by simp

  from new_match \<open>v \<in> Vs M'\<close> have "?i \<noteq> v" "j \<noteq> v" "j \<in> Vs G" "?i \<in> Vs G"
    by auto

  from \<open>?i \<noteq> v\<close> \<open>?i \<in> Vs G\<close> \<open>v \<in> Vs G\<close> have "Vs_enum ?i \<noteq> Vs_enum v"
    by (intro Vs_enum_neqI)

  from \<open>j \<noteq> v\<close> \<open>j \<in> Vs G\<close> \<open>v \<in> Vs G\<close> have "Vs_enum j \<noteq> Vs_enum v"
    by (intro Vs_enum_neqI)

  with assms step \<open>Vs_enum ?i \<noteq> Vs_enum v\<close> show ?thesis
    by auto
qed (use assms in simp_all)

lemma ranking_dual_matched_previously:
  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"

  assumes "v \<in> Vs M'"
  assumes "v \<in> Vs G"

  shows "d $ Vs_enum v = d' $ Vs_enum v"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  from Cons.prems have "d $ Vs_enum v = (snd \<circ> snd) ?step $ Vs_enum v"
  proof (intro Cons.IH[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step"], goal_cases)
    case 2
    then show ?case
      by (simp add: fst_step_primal_dual step_mono_vs)
  qed (simp_all add: ranking_primal_dual_Cons)

  also from Cons.prems have "\<dots> = d' $ Vs_enum v"
    by (intro step_dual_matched_previously[where M' = M' and p' = p' and M = "fst ?step" and p = "(fst \<circ> snd) ?step"])
       auto

  finally show ?case .
qed simp

lemma step_dual_matched_L:
  assumes "dim_vec d' = n"

  assumes step_result: "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "l \<notin> Vs M'"
  assumes "l \<in> Vs M"
  assumes "l \<in> L"
  assumes "j \<in> R"

  shows "d $ Vs_enum l = (g \<circ> Y) l / F"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match have step: "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1,
    d' |\<^sub>v Vs_enum ?i \<mapsto> (g \<circ> Y) ?i / F |\<^sub>v Vs_enum j \<mapsto> (1 - (g \<circ> Y) ?i) / F
  )"
    by simp

  from \<open>l \<in> L\<close> \<open>j \<in> R\<close> bipartite have "l \<noteq> j" "Vs_enum l < n"
    by (auto dest: bipartite_disjointD L_enum_less_n)

  with parts_minimal \<open>l \<in> L\<close> \<open>j \<in> R\<close> have "Vs_enum l \<noteq> Vs_enum j"
    by (intro Vs_enum_neqI) auto

  from assms step \<open>l \<noteq> j\<close> have "l = ?i"
    by (auto simp: vs_insert)    

  with step_result step \<open>dim_vec d' = n\<close> \<open>Vs_enum l \<noteq> Vs_enum j\<close> \<open>Vs_enum l < n\<close> show ?thesis
    by auto
qed (use assms in simp_all)

lemma ranking_dual_matched_L:
  assumes "dim_vec d' = n"

  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  assumes "l \<notin> Vs M'"
  assumes "l \<in> Vs M"
  assumes "l \<in> L"
  assumes "set js \<subseteq> R"

  shows "d $ Vs_enum l = (g \<circ> Y) l / F"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  show ?case
  proof (cases "l \<in> Vs (fst ?step)")
    case True

    with Cons.prems parts_minimal have "d $ Vs_enum l = (snd \<circ> snd) ?step $ Vs_enum l"
      by (intro ranking_dual_matched_previously[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step" and js = js and M = M and p = p and d = d], goal_cases)
         (simp_all add: ranking_primal_dual_Cons)

    also from Cons.prems True have "\<dots> = (g \<circ> Y) l / F"
      by (intro step_dual_matched_L[where d' = d' and M' = M' and p' = p' and j = j and M = "fst ?step" and p = "(fst \<circ> snd) ?step"])
         simp_all

    finally show ?thesis .
  next
    case False
    with Cons.prems show ?thesis
      by (intro Cons.IH[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step" and d' = "(snd \<circ> snd) ?step"])
         (simp_all add: ranking_primal_dual_Cons)
  qed
qed simp

lemma step_dual_matched_R:
  assumes "dim_vec d' = n"

  assumes step_result: "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "r \<notin> Vs M'"
  assumes "r \<in> Vs M"
  assumes "r \<in> R"
  assumes "j \<in> R"

  shows "d $ Vs_enum r = (1 - (g \<circ> Y) (THE i. {i,r} \<in> M)) / F"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match have step: "step_primal_dual (M',p',d') j = (
    insert {?i,j} M',
    p' |\<^sub>v G_enum {?i,j} \<mapsto> 1,
    d' |\<^sub>v Vs_enum ?i \<mapsto> (g \<circ> Y) ?i / F |\<^sub>v Vs_enum j \<mapsto> (1 - (g \<circ> Y) ?i) / F
  )"
    by simp

  with assms new_match bipartite have "r = j"
    by (auto simp: vs_insert dest: bipartite_edgeD)

  from \<open>j \<in> R\<close> have "Vs_enum j < n"
    by (auto intro: R_enum_less_n)

  have "(THE i. {i,j} \<in> M) = ?i"
  proof (intro the_equality, goal_cases)
    case 1
    from step step_result show ?case
      by simp
  next
    case (2 i)
    from step_result have "M = insert {?i,j} M'"
      by (simp add: step)

    with 2 \<open>j \<notin> Vs M'\<close> show ?case
      by (auto simp add: doubleton_eq_iff)
  qed

  with step step_result \<open>dim_vec d' = n\<close> \<open>r = j\<close> \<open>Vs_enum j < n\<close> show ?thesis
    by simp
qed (use assms in simp_all)

lemma step_primal_dual_Ex1:
  assumes "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "\<exists>!l. {l,r} \<in> M'"
  shows "\<exists>!l. {l,r} \<in> M"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match assms have "M = insert {?i,j} M'"
    by simp

  with new_match assms show ?thesis
    by (auto simp add: doubleton_eq_iff dest: edges_are_Vs)
qed (use assms in simp_all)

lemma step_primal_dual_the_match:
  assumes "step_primal_dual (M',p',d') j = (M,p,d)"
  assumes "\<exists>!l. {l,r} \<in> M'"
  shows "(THE i. {i,r} \<in> M) = (THE i. {i,r} \<in> M')"
  using step_primal_dual_cases[of M' j]
proof cases
  case new_match
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
  let ?i = "arg_min_on Y ?ns"

  from new_match \<open>\<exists>!l. {l,r} \<in> M'\<close> have "r \<noteq> j" "r \<noteq> ?i"
    by (auto dest: edges_are_Vs)

  from new_match assms have "M = insert {?i,j} M'"
    by simp

  with assms \<open>r \<noteq> j\<close> \<open>r \<noteq> ?i\<close> show ?thesis
    by (simp add: doubleton_eq_iff)
qed (use assms in simp_all)

lemma ranking_primal_dual_the_match:
  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  assumes "r \<in> Vs M'"
  assumes "\<exists>!l. {l,r} \<in> M'"
  shows "(THE i. {i,r} \<in> M) = (THE i. {i,r} \<in> M')"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"

  from Cons.prems have "(THE i. {i,r} \<in> M) = (THE i. {i,r} \<in> fst ?step)"
  proof (intro Cons.IH[where p' = "(fst \<circ> snd) ?step" and d' = "(snd \<circ> snd) ?step"], goal_cases)
    case 1
    then show ?case
      by (simp add: ranking_primal_dual_Cons)
  next
    case 2
    then show ?case
      by (simp add: fst_step_primal_dual step_mono_vs)
  next
    case 3
    show ?case
      by (rule step_primal_dual_Ex1[where M' = M' and p' = p' and d' = d' and j = j and p = "(fst \<circ> snd) ?step" and d = "(snd \<circ> snd) ?step"])
         (use 3 in simp_all)
  qed

  also from Cons.prems have "\<dots> = (THE i. {i,r} \<in> M')"
    by (intro step_primal_dual_the_match[where p' = p' and d' = d' and j = j and p = "(fst \<circ> snd) ?step" and d = "(snd \<circ> snd) ?step"])
       auto

  finally show ?case .
qed simp

lemma ranking_dual_matched_R:
  assumes "dim_vec d' = n"

  assumes "ranking_primal_dual' (M',p',d') js = (M,p,d)"
  assumes "r \<notin> Vs M'"
  assumes "r \<in> Vs M"
  assumes "r \<in> R"
  assumes "set js \<subseteq> R"

  shows "d $ Vs_enum r = (1 - (g \<circ> Y) (THE i. {i,r} \<in> M)) / F"
  using assms
proof (induction js arbitrary: M' p' d')
  case (Cons j js)
  let ?step = "step_primal_dual (M',p',d') j"
  
  show ?case
  proof (cases "r \<in> Vs (fst ?step)")
    case True

    with Cons.prems have the_match: "(THE i. {i,r} \<in> M) = (THE i. {i,r} \<in> fst ?step)"
    proof (intro ranking_primal_dual_the_match[where p' = "(fst \<circ> snd) ?step" and d' = "(snd \<circ> snd) ?step" and js = js and p = p and d = d], goal_cases)
      case 3
      show ?case
        using step_primal_dual_cases[of M' j]
      proof cases
        case new_match
        with Cons.prems True show ?thesis
          by (auto simp add: doubleton_eq_iff vs_insert)
      qed (use Cons.prems True in force)+
    qed (simp_all add: ranking_primal_dual_Cons)

    from True Cons.prems parts_minimal \<open>r \<in> R\<close> have "d $ Vs_enum r = ((snd \<circ> snd) ?step) $ Vs_enum r"
      by (intro ranking_dual_matched_previously[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step" and js = js and M = M and p = p], goal_cases)
         (auto simp: ranking_primal_dual_Cons)

    also from True Cons.prems have "\<dots> = (1 - (g \<circ> Y) (THE i. {i,r} \<in> fst ?step)) / F"
      by (intro step_dual_matched_R[where M' = M' and p' = p' and d' = d' and j = j and p = "(fst \<circ> snd) ?step"])
         simp_all

    also have "\<dots> = (1 - (g \<circ> Y) (THE i. {i,r} \<in> M)) / F"
      by (simp add: the_match)

    finally show ?thesis .
  next
    case False
    with Cons.prems show ?thesis
      by (intro Cons.IH[where M' = "fst ?step" and p' = "(fst \<circ> snd) ?step" and d' = "(snd \<circ> snd) ?step"])
         (simp_all add: ranking_primal_dual_Cons)
  qed
qed simp

lemma ranking_primal_One_iff:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "e \<in> G"
  shows "p $ G_enum e = 1 \<longleftrightarrow> e \<in> M"
  using assms
  by (metis empty_iff graph_abs_G.finite_E index_zero_vec(1) index_zero_vec(2) m_def ranking_primal_matched ranking_primal_unmatched to_nat_on_less_card zero_neq_one)

lemma ranking_primal_Zero_iff:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "e \<in> G"
  shows "p $ G_enum e = 0 \<longleftrightarrow> e \<notin> M"
  using assms
  by (metis graph_abs_G.finite_E index_zero_vec(1) m_def ranking_primal_One_iff ranking_primal_unmatched to_nat_on_less_card zero_neq_one)

lemma ranking_dual_L_if_matched:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "l \<in> L"
  assumes "set js \<subseteq> R"
  shows "l \<in> Vs M \<Longrightarrow> d $ Vs_enum l = (g \<circ> Y) l / F"
  using assms
  by (intro ranking_dual_matched_L) auto

lemma ranking_dual_R_if_matched:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "r \<in> R"
  assumes "set js \<subseteq> R"
  shows "r \<in> Vs M \<Longrightarrow> d $ Vs_enum r = (1 - (g \<circ> Y) (THE i. {i,r} \<in> M)) / F"
  using assms
  by (intro ranking_dual_matched_R) auto

lemma ranking_dual_if_unmatched:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "v \<in> Vs G"
  shows "v \<notin> Vs M \<Longrightarrow> d $ Vs_enum v = 0"
  using assms
  by (metis L_enum_less_n R_enum_less_n Un_iff Vs_enum_def index_zero_vec(1) parts_minimal ranking_dual_unmatched)

lemma vec_eqI:
  assumes "dim_vec v = dim_vec v'"
  assumes "\<And>i. i < dim_vec v \<Longrightarrow> v $ i = v' $ i"
  shows "v = v'"
  using assms
  by auto

lemma primal_sol_eq:
  assumes "ranking_primal_dual js = (M,p,d)"
  shows "p = primal_sol M"
  using assms
  apply (intro vec_eqI)
  unfolding primal_sol_def
   apply (metis dim_vec dim_vec_ranking_primal_dual(1) fst_conv index_zero_vec(2) snd_conv)
  by (smt (verit, best) card.empty dim_vec_ranking_primal_dual(1) from_nat_into fst_conv graph_abs_G.finite_E index_vec index_zero_vec(1) index_zero_vec(2) m_def not_less_zero of_bool_eq(1) of_bool_eq(2) ranking_primal_One_iff ranking_primal_unmatched snd_conv to_nat_on_from_nat_into_less)

lemma dual_sol_eq:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "set js \<subseteq> R"

  shows "d = dual_sol M"
proof (intro vec_eqI, goal_cases)
  case (2 i)
  with assms consider (unmatched) "Vs_enum_inv i \<notin> Vs M" | 
    (L) "Vs_enum_inv i \<in> Vs M" "i < card L" | (R) "Vs_enum_inv i \<in> Vs M" "card L \<le> i" "i < n"
    by fastforce
  then show ?case
  proof cases
    case unmatched
    with 2 assms show ?thesis
      apply (auto simp: dual_sol_def)
      by (metis UnCI Vs_enum_inv Vs_enum_inv_def add.right_neutral card.empty from_nat_into less_zeroE n_sum parts_minimal ranking_dual_if_unmatched)
  next
    case L
    with 2 assms show ?thesis
      apply (auto simp: dual_sol_def)
      by (metis Vs_enum_inv Vs_enum_inv_def card.empty comp_apply from_nat_into not_less_zero ranking_dual_L_if_matched)
  next
    case R
    let ?r = "Vs_enum_inv i"
    from R assms have "d $ Vs_enum (Vs_enum_inv i) = (1 - (g \<circ> Y) (THE i. {i,?r} \<in> M)) / F"
      apply (intro ranking_dual_R_if_matched[where r = ?r and p = p and js =js])
         apply auto
      by (metis card.empty from_nat_into geq_L_less_n_less_R not_less_zero)

    with 2 R show ?thesis
      apply (auto simp: dual_sol_def)
      by (metis Vs_enum_inv Vs_enum_inv_def linorder_not_le)
  qed
qed (use assms in simp)

lemma ranking_primal_card:
  assumes "ranking_primal_dual js = (M,p,d)"
  shows "p \<bullet> 1\<^sub>v m = card M"
  using assms
  apply (auto simp: primal_sol_eq[OF assms] intro!: primal_dot_One_card)
  apply (metis empty_subsetI fst_conv fst_ranking_primal_dual graph_abs_G.graph in_mono subgraph_ranking)
  done

lemma ranking_dual_card:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "set js \<subseteq> R"

  shows "d \<bullet> 1\<^sub>v n = card M / F"
  using assms
  apply (auto simp: dual_sol_eq[OF assms] intro!: dual_dot_One_card)
   apply (metis empty_subsetI fst_conv fst_ranking_primal_dual graph_abs_G.graph in_mono subgraph_ranking)
  by (metis fst_conv fst_ranking_primal_dual graph_abs_G.graph matching_empty matching_ranking)

lemma ranking_primal_dual_F:
  assumes "ranking_primal_dual js = (M,p,d)"
  assumes "set js \<subseteq> R"

  shows "p \<bullet> 1\<^sub>v m = d \<bullet> 1\<^sub>v n * F"
  using assms F_neq_0
  by (auto simp: ranking_primal_card ranking_dual_card)
end


end