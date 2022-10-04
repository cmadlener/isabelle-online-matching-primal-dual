theory Ranking_Order_Probabilistic
  imports
    Ranking_Order
    Order_Relations_From_Priorities
    Bipartite_Vertex_Priorities
begin

hide_type Finite_Cartesian_Product.vec
hide_const Finite_Cartesian_Product.vec Finite_Cartesian_Product.vec.vec_nth

locale wf_ranking_order_prob = bipartite_vertex_priorities +
  fixes \<pi> :: "'a list"
  fixes g :: "real \<Rightarrow> real" and F :: real

  assumes perm: "\<pi> \<in> permutations_of_set R"

  assumes g_funcset: "g \<in> {0..1} \<rightarrow> {0..1}"
  assumes g_mono: "mono_on g {0..1}"
  assumes g_One: "g 1 = 1"
  assumes g_borel[measurable]: "g \<in> borel_measurable borel"

  assumes g_integral_bound: "0 \<le> \<theta> \<Longrightarrow> \<theta> \<le> 1 \<Longrightarrow> \<integral>y. g y * indicator {0..<\<theta>} y \<partial>uniform_measure lborel {0..1} + 1 - g \<theta> \<ge> F"

  assumes F_gt_0: "0 < F"
begin

definition dual_sol :: "('a \<Rightarrow> real) \<Rightarrow> 'a graph \<Rightarrow> real vec" where
  "dual_sol Y M \<equiv> vec n (\<lambda>i.
    if Vs_enum_inv i \<in> Vs M
    then
      if i < card L then (g \<circ> Y) (Vs_enum_inv i) / F
      else (1 - (g \<circ> Y) (THE l. {l, Vs_enum_inv i} \<in> M)) / F
    else 0
  )"

definition y\<^sub>c :: "('a \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
  "y\<^sub>c Y js i j \<equiv>
    if j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) js)
    then Y (THE i'. {i',j} \<in> ranking (linorder_from_keys L Y) (G \<setminus> {i}) js)
    else 1"

lemma g_nonnegI: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> g x"
  using g_funcset
  by auto

lemma g_less_eq_OneI: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> g x \<le> 1"
  using g_funcset
  by auto

lemma div_F_nonneg[simp]: "0 \<le> x / F \<longleftrightarrow> 0 \<le> x"
  using F_gt_0
  by (simp add: zero_le_divide_iff)

lemma div_F_less_eq_cancel[simp]: "x / F \<le> y / F \<longleftrightarrow> x \<le> y"
  using F_gt_0
  by (simp add: divide_le_cancel)

lemma dim_dual_sol[simp]: "dim_vec (dual_sol Y M) = n"
  by (simp add: dual_sol_def)

lemma dual_dot_One_card:
  assumes "M \<subseteq> G"
  assumes "matching M"
  shows "1\<^sub>v n \<bullet> dual_sol Y M = card M / F"
proof -
  from graph have "1\<^sub>v n \<bullet> dual_sol Y M = 
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

    from bipartite_graph e obtain l r where e': "e = {l,r}" "l \<in> L" "r \<in> R"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    from i have "Vs_enum_inv i \<in> L"
      by (auto elim: Vs_enum_inv_leftE)

    with bipartite_graph e e' have the_l: "(THE l. l \<in> L \<and> l \<in> e) = Vs_enum_inv i"
      by (auto dest: bipartite_disjointD)

    with i_less_n show "Vs_enum (THE l. l \<in> L \<and> l \<in> (THE e. e \<in> M \<and> local.Vs_enum_inv i \<in> e)) = i"
      by (auto simp: the_e the_l)

    show "g (Y (THE l. l \<in> L \<and> l \<in> (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e))) / F = g (Y (Vs_enum_inv i)) / F"
      by (simp add: the_e the_l)
  next
    fix e
    assume eM: "e \<in> M"

    with bipartite_graph obtain l r where e: "e = {l,r}" "l \<in> L" "r \<in> R"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    with bipartite_graph have the_l: "(THE l. l \<in> L \<and> l \<in> e) = l"
      by (auto dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>] bipartite_disjointD)

    from eM \<open>e = {l,r}\<close> \<open>matching M\<close> have the_e: "(THE e. e \<in> M \<and> l \<in> e) = e"
      by (intro the_equality matching_unique_match) auto

    from parts_minimal \<open>l \<in> L\<close> have "l \<in> Vs G"
      by blast

    then show "(THE e'. e' \<in> M \<and> Vs_enum_inv (Vs_enum (THE l. l \<in> L \<and> l \<in> e)) \<in> e') = e"
      by (simp add: the_l Vs_inv_enum the_e)

    from eM e have "l \<in> Vs M"
      by (auto dest: edges_are_Vs)

    with eM \<open>l \<in> L\<close> show "Vs_enum (THE l. l \<in> L \<and> l \<in> e) \<in> {0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> {i. i < card L}"
      by (auto simp: the_l intro: Vs_enum_less_n_L Vs_enum_less_card_L)
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

    from bipartite_graph e obtain l r where e': "e = {l,r}" "l \<in> L" "r \<in> R"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    from i have "Vs_enum_inv i \<in> R"
      by (auto elim: Vs_enum_inv_rightE)

    with e' e parts_minimal have the_r: "(THE r. r \<in> R \<and> r \<in> e) = Vs_enum_inv i"
      by (auto elim: Vs_cases)

    from i_less_n show "Vs_enum (THE r. r \<in> R \<and> r \<in> (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e)) = i"
      by (simp add: the_e the_r)

    from e e' bipartite_graph have the_l: "(THE l. l \<in> L \<and> l \<in> e) = l"
      by (intro the_equality)
         (auto dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>] bipartite_disjointD)

    from e e' \<open>matching M\<close> \<open>Vs_enum_inv i \<in> R\<close> have the_l': "(THE l. {l, Vs_enum_inv i} \<in> M) = l"
      by (auto intro: the_match)

    show "(1 - g (Y (THE l. l \<in> L \<and> l \<in> (THE e. e \<in> M \<and> Vs_enum_inv i \<in> e)))) / F = (1 - g (Y (THE l. {l, Vs_enum_inv i} \<in> M))) / F"
      by (simp add: the_e the_l the_l')
  next
    fix e
    assume eM: "e \<in> M"

    with bipartite_graph obtain l r where e: "e = {l,r}" "l \<in> L" "r \<in> R" "l \<noteq> r"
      by (auto elim: bipartite_edgeE dest: bipartite_subgraph[OF _ \<open>M \<subseteq> G\<close>])

    with bipartite_graph have the_r: "(THE r. r \<in> R \<and> r \<in> e) = r"
      by (intro the_equality)
         (auto dest: bipartite_disjointD)

    from eM \<open>e = {l,r}\<close> \<open>matching M\<close> have the_e: "(THE e. e \<in> M \<and> r \<in> e) = e"
      by (intro the_equality matching_unique_match)
         auto

    from \<open>r \<in> R\<close> show "(THE e'. e' \<in> M \<and> Vs_enum_inv (Vs_enum (THE r. r \<in> R \<and> r \<in> e)) \<in> e') = e"
      by (simp add: the_r the_e)

    from eM e have "r \<in> Vs M"
      by (auto dest: edges_are_Vs)

    with \<open>r \<in> R\<close> show "Vs_enum (THE r. r \<in> R \<and> r \<in> e) \<in> {0..<n} \<inter> {i. Vs_enum_inv i \<in> Vs M} \<inter> - {i. i < card L}"
      by (auto simp: the_r intro: Vs_enum_less_n_R dest: Vs_enum_geq_card_L)
  qed

  with graph L_sum_matching show ?thesis
    by (auto simp: scalar_prod_def dual_sol_def n_def sum.If_cases simp flip: sum.distrib add_divide_distrib)
qed

lemma primal_is_dual_times_F:
  assumes "M \<subseteq> G"
  assumes "matching M"
  shows "1\<^sub>v m \<bullet> primal_sol M = 1\<^sub>v n \<bullet> dual_sol Y M * F"
  using assms F_gt_0
  by (auto simp: primal_dot_One_card dual_dot_One_card)

lemma preorder_on_neighbors_linorder_from_keys[intro]:
  assumes "H \<subseteq> G"
  assumes "j \<in> R"
  shows "preorder_on' {i. {i,j} \<in> H} (linorder_from_keys L Y)"
  using assms perm
  by (auto dest: permutations_of_setD)

lemma set_\<pi>[simp]: "set \<pi> = R"
  using perm
  by (auto dest: permutations_of_setD)

lemma ranking_fun_upd_remove_eq:
  assumes "set js \<subseteq> R"
  shows "ranking (linorder_from_keys L (Y(i:=y))) (G \<setminus> {i}) js = ranking (linorder_from_keys L Y) (G \<setminus> {i}) js"
  (is "?L = ?R")
proof -
  from assms have "?L = ranking (Restr (linorder_from_keys L (Y(i := y))) (L - {i})) (G \<setminus> {i}) js"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: preorder_on_imp_preorder_on')
    
  also have "\<dots> = ranking (linorder_from_keys (L - {i}) (Y)) (G \<setminus> {i}) js" (is "_ = ?M")
    by (simp add: linorder_from_keys_Restr linorder_from_keys_update_eq)

  finally have "?L = ?M" .

  from assms have "?R = ranking (Restr (linorder_from_keys L Y) (L - {i})) (G \<setminus> {i}) js"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: preorder_on_imp_preorder_on')

  also have "\<dots> = ?M"
    by (simp add: linorder_from_keys_Restr)

  finally show ?thesis
    by (simp add: \<open>?L = ?M\<close>)
qed

lemma y\<^sub>c_fun_upd_eq:
  assumes "j \<in> R"
  shows "y\<^sub>c (Y(i:=y)) \<pi> i j = y\<^sub>c Y \<pi> i j"
proof -
  let ?M' = "ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>"
  have "j \<in> Vs ?M' \<Longrightarrow> (THE i'. {i',j} \<in> ?M') = i \<Longrightarrow> False"
  proof -
    assume "j \<in> Vs ?M'" 
    assume the_i'_eq: "(THE i'. {i',j} \<in> ?M') = i"

    from \<open>j \<in> R\<close> \<open>j \<in> Vs ?M'\<close> have the_i'_M: "{(THE i'. {i',j} \<in> ?M'), j} \<in> ?M'"
      by (intro the_ranking_match_left)
         (auto dest: remove_vertices_subgraph')

    have "{(THE i'. {i',j} \<in> ?M'), j} \<in> G \<setminus> {i}"
      by (auto intro: ranking_subgraph'[OF _ _ _ the_i'_M] dest: remove_vertices_subgraph')

    then have "(THE i'. {i',j} \<in> ?M') \<in> Vs (G \<setminus> {i})"
      by (auto dest: edges_are_Vs)

    with the_i'_eq show False
      by (auto intro: remove_vertices_not_vs')
  qed

  then show ?thesis
    unfolding y\<^sub>c_def
    by (auto simp: ranking_fun_upd_remove_eq)
qed

lemma the_ranking_match_remove_left:
  assumes "j \<in> R"
  assumes "j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)"
  shows "(THE i'. {i',j} \<in> ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>) \<in> L - {i}"
proof -
  let ?M = "ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>"

  from assms have the_i': "{(THE i'. {i',j} \<in> ?M), j} \<in> ?M"
    "(THE i'. {i',j} \<in> ?M) \<in> L"
    by (auto intro!: the_ranking_match_left dest: remove_vertices_subgraph')

  have subg: "?M \<subseteq> G \<setminus> {i}"
    by (intro ranking_subgraph) (auto dest: remove_vertices_subgraph')

  with the_i' show "(THE i'. {i',j} \<in> ?M) \<in> L - {i}"
    by (auto dest!: subsetD edges_are_Vs(1)[of i j] intro: remove_vertices_not_vs'[where X = "{i}"])
qed

lemma y\<^sub>c_bounded: 
  assumes "j \<in> R"
  assumes "Y \<in> L-{i} \<rightarrow> {0..1}"
  shows "y\<^sub>c Y \<pi> i j \<in> {0..1}"
proof (cases "j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)")
  case True

  with assms \<open>j \<in> R\<close> show ?thesis
    by (auto simp: y\<^sub>c_def dest: the_ranking_match_remove_left)
qed (simp add: y\<^sub>c_def)

\<comment> \<open>Lemma 2 from DJK\<close>
lemma dominance:
  assumes "linorder_on L (linorder_from_keys L Y)"
  assumes "i \<in> L" "j \<in> R"
  assumes "{i,j} \<in> G"

  assumes "Y i < y\<^sub>c Y \<pi> i j"
  shows "i \<in> Vs (ranking (linorder_from_keys L Y) G \<pi>)"
proof (intro dominance_order[where j = j], goal_cases)
  case 6    
  with perm \<open>Y i < y\<^sub>c Y \<pi> i j\<close> \<open>i \<in> L\<close> \<open>j \<in> R\<close> show ?case
    by (intro linorder_from_keys_lessI the_ranking_match_left ballI preorder_on_neighborsI)
       (auto simp: y\<^sub>c_def dest: remove_vertices_subgraph')
qed (use assms in auto)

\<comment> \<open>Lemma 3 from DJK\<close>
lemma monotonicity:
  assumes linorder: "linorder_on L (linorder_from_keys L Y)"
  assumes "Y \<in> L \<rightarrow> {0..1}"
  assumes "i \<in> L" "j \<in> R"
  assumes "{i,j} \<in> G"

  shows "dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ Vs_enum j \<ge> (1 - g (y\<^sub>c Y \<pi> i j)) / F"
    (is "dual_sol Y ?M $ ?j \<ge> ?\<beta>")
proof (cases "j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)")
  case True
  let ?M' = "ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>"

  from \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have index_j: "?j < n" "\<not> ?j < card L"
    by (auto intro: Vs_enum_less_n dest: edges_are_Vs, simp add: Vs_enum_R)

  have j_matched: "j \<in> Vs ?M"
  proof -
    from perm \<open>j \<in> R\<close> obtain pre suff where \<pi>_decomp: "\<pi> = pre @ j # suff" "j \<notin> set pre" "j \<notin> set suff"
      by (metis permutations_of_setD split_list_distinct)

    let ?ranking_pre = "ranking (linorder_from_keys L Y) G pre"
    let ?ranking_pre' = "ranking (linorder_from_keys L Y) (G \<setminus> {i}) pre"

    from \<pi>_decomp perm \<open>j \<in> R\<close> have j_unmatched_pre: "j \<notin> Vs ?ranking_pre"
      by (intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI)
         (auto dest: permutations_of_setD)

    from \<pi>_decomp perm \<open>j \<in> R\<close> have j_unmatched_pre': "j \<notin> Vs ?ranking_pre'"
      by (intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI)
         (auto dest: permutations_of_setD remove_vertices_subgraph')

    let ?ns = "{i. i \<notin> Vs ?ranking_pre \<and> {i,j} \<in> G}"
    and ?ns' = "{i'. i' \<notin> Vs ?ranking_pre' \<and> {i',j} \<in> G \<setminus> {i}}"

    from \<open>j \<in> R\<close> have "?ns \<subseteq> L"
      by (intro unmatched_neighbors_L subset_refl)

    from \<open>j \<in> R\<close> have "?ns' \<subseteq> L - {i}"
      by (auto dest: neighbors_right_subset_left[OF remove_vertices_subgraph] edges_are_Vs intro: remove_vertices_not_vs')

    have "?ns' \<noteq> {}"
    proof (rule ccontr, simp only: not_not)
      assume "?ns' = {}"

      then have step_eq: "step (linorder_from_keys L Y) (G \<setminus> {i}) ?ranking_pre' j = ?ranking_pre'"
        by (simp add: step_def)

      from j_unmatched_pre' \<pi>_decomp perm \<open>j \<in> R\<close> have "j \<notin> Vs ?M'"
        by (simp only: \<pi>_decomp ranking_append ranking_Cons step_eq,
            intro unmatched_R_in_ranking_if[where M = ?ranking_pre'] ballI preorder_on_neighborsI)
           (auto dest: remove_vertices_subgraph' permutations_of_setD)

      with True show False
        by blast
    qed

    from linorder perm \<pi>_decomp \<open>i \<in> L\<close> have "L - {i} - Vs ?ranking_pre' \<subseteq> L - Vs ?ranking_pre"
      by (intro monotonicity_order_ranking ballI linorder_on_neighborsI)
         (auto dest: permutations_of_setD)
      
    with \<open>?ns \<subseteq> L\<close> \<open>?ns' \<subseteq> L - {i}\<close> have "?ns' \<subseteq> ?ns"
      by (auto dest: remove_vertices_subgraph')

    with \<open>?ns' \<noteq> {}\<close> obtain i' where "i' \<in> ?ns"
      by blast

    then have "{i',j} \<in> G" "i' \<notin> Vs ?ranking_pre"
      by auto

    with j_unmatched_pre have "j \<in> Vs (step (linorder_from_keys L Y) G ?ranking_pre j)"
      by (intro step_matches_if_possible[OF j_unmatched_pre \<open>{i',j} \<in> G\<close>])
         auto

    with \<pi>_decomp show "j \<in> Vs ?M"
      by (auto simp: ranking_append ranking_Cons intro: ranking_mono_vs)
  qed

  have bipartite_M: "bipartite ?M L R" and bipartite_M': "bipartite ?M' L R"
    by (auto intro!: bipartite_ranking dest: remove_vertices_subgraph')

  with j_matched True obtain i' i'' where edges: "{i',j} \<in> ?M" "{i'',j} \<in> ?M'"
    by (meson finite_L finite_R finite_parts_bipartite_graph_abs graph_abs_vertex_edgeE')

  with bipartite_M bipartite_M' \<open>j \<in> R\<close> have i_left: "i' \<in> L" "i'' \<in> L"
    by (auto dest: bipartite_edgeD)

  have "matching ?M" and "matching ?M'"
    by (auto intro!: matching_ranking dest: remove_vertices_subgraph')

  with \<open>{i',j} \<in> ?M\<close> \<open>{i'',j} \<in> ?M'\<close> have the_i': "(THE i. {i,j} \<in> ?M) = i'" and the_i'': "(THE i'. {i',j} \<in> ?M') = i''"
    by (auto intro: the_match)

  from linorder perm edges \<open>{i,j} \<in> G\<close> \<open>i \<in> L\<close> \<open>j \<in> R\<close> have "(i',i'') \<in> linorder_from_keys L Y"
    by (intro monotonicity_order_matched_matched) (auto dest: permutations_of_setD)

  then have "Y i' \<le> Y i''"
    unfolding linorder_from_keys_def
    by simp
  
  with True j_matched index_j i_left g_mono \<open>{i,j} \<in> G\<close> \<open>Y \<in> L \<rightarrow> {0..1}\<close> \<open>j \<in> R\<close> show ?thesis
    unfolding y\<^sub>c_def dual_sol_def
    by (auto simp: the_i' the_i'' dest: mono_onD)
next
  case False
  note j_unmatched' = this

  from \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have index_j: "?j < n" "\<not> ?j < card L"
    by (auto intro: Vs_enum_less_n dest: edges_are_Vs, simp add: Vs_enum_R)
  show ?thesis
  proof (cases "j \<in> Vs ?M")
    case True

    with \<open>j \<in> R\<close> have "(THE l. {l, j} \<in> ranking (linorder_from_keys L Y) G \<pi>) \<in> L"
      by (intro the_ranking_match_left) auto

    with True j_unmatched' index_j F_gt_0 \<open>{i,j} \<in> G\<close> \<open>Y \<in> L \<rightarrow> {0..1}\<close> show ?thesis
      unfolding y\<^sub>c_def dual_sol_def
      by (auto simp: g_One dest!: edges_are_Vs intro: divide_nonneg_pos intro!: g_less_eq_OneI)
  next
    case False
    
    with j_unmatched' index_j F_gt_0 \<open>{i,j} \<in> G\<close> show ?thesis
      unfolding y\<^sub>c_def dual_sol_def
      by (auto simp: g_One dest: edges_are_Vs intro: divide_nonneg_pos)
  qed
qed

lemma ranking_measurable':
  assumes "H \<subseteq> G"
  assumes "set js \<subseteq> R"
  shows "(\<lambda>Y. ranking (linorder_from_keys L Y) H js) \<in> M\<^sub>Y \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys L" _ "count_space (preorders_on L)"], goal_cases)
  case 1
  from finite_L show ?case
    by measurable
next
  case 2
  from finite_subsets \<open>set js \<subseteq> R\<close> \<open>H \<subseteq> G\<close> show ?case
    by (subst measurable_count_space_eq2)
       (auto dest: ranking_subgraph' preorders_onD)
qed

lemma ranking_measurable_remove_vertices:
  assumes "set js \<subseteq> R"
  shows "(\<lambda>Y. ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) js) \<in> (\<Pi>\<^sub>M i \<in> L - X. U) \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys (L - X)" _ "count_space (preorders_on (L - X))"], goal_cases)
  case 1
  from finite_L have "finite (L - X)" by blast
  then show ?case
    by measurable
next
  case 2
  from \<open>set js \<subseteq> R\<close> have "preorder_on (L - X) r \<Longrightarrow> ranking r (G \<setminus> X) js \<subseteq> G \<setminus> X" for r
    by (intro Ranking_Order.ranking_subgraph) auto

  with finite_subsets finite_vs show ?case
    by (auto dest: preorders_onD remove_vertices_subgraph')
qed

lemmas ranking_measurable = ranking_measurable'[OF subset_refl]

lemma ranking_measurable_fun_upd:
  assumes "i \<in> L"
  assumes "set js \<subseteq> R"
  assumes "Y \<in> space (Pi\<^sub>M (L - {i}) (\<lambda>_. U))"
  shows "(\<lambda>y. ranking (linorder_from_keys L (Y(i:=y))) G js) \<in> U \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
  by (rule measurable_compose[OF measurable_fun_upd[where I = L and J = "L - {i}" and M = "\<lambda>_.U"]])
     (use assms finite_L in \<open>auto intro: ranking_measurable\<close>)

lemma in_vertices_borel_measurable_count_space:
  "(\<lambda>M. i \<in> Vs M) \<in> borel_measurable (count_space {M. M \<subseteq> G})"
  by measurable

lemma in_vertices_Measurable_pred_count_space:
  "Measurable.pred (count_space {M. M \<subseteq> G}) (\<lambda>M. i \<in> Vs M)"
  by measurable

lemmas in_vertices_borel_measurable[measurable] = measurable_compose[OF ranking_measurable' in_vertices_borel_measurable_count_space]
lemmas in_vertices_Measurable_pred[measurable] = measurable_compose[OF ranking_measurable' in_vertices_Measurable_pred_count_space]

lemmas in_vertices_borel_measurable_remove_vertices[measurable] = measurable_compose[OF ranking_measurable_remove_vertices in_vertices_borel_measurable_count_space]
lemmas in_vertices_Measurable_pred_remove_vertices[measurable] = measurable_compose[OF ranking_measurable_remove_vertices in_vertices_Measurable_pred_count_space]

lemmas in_vertices_borel_measurable_fun_upd[measurable] = measurable_compose[OF ranking_measurable_fun_upd in_vertices_borel_measurable_count_space]
lemmas in_vertices_Measurable_pred_fun_upd[measurable] = measurable_compose[OF ranking_measurable_fun_upd in_vertices_Measurable_pred_count_space]

lemma online_matched_with_borel_iff:
  fixes Y :: "'a \<Rightarrow> real" and X :: "'a set"
  defines "r \<equiv> linorder_from_keys (L - X) Y"
  assumes "j \<in> R" "A \<in> sets borel"

  \<comment> \<open>should we lift this assumption (since it is always true)? would need to use \<^term>\<open>takeWhile (\<lambda>x. x \<noteq> j)\<close>
      and \<^term>\<open>dropWhile\<close> in statement\<close>
  assumes \<pi>_decomp: "\<pi> = \<pi>' @ j # \<pi>''" "j \<notin> set \<pi>'" "j \<notin> set \<pi>''"
  defines "M' \<equiv> ranking r (G \<setminus> X) \<pi>'"

  shows "j \<in> Vs (ranking r (G \<setminus> X) \<pi>) \<and> Y (THE i. {i,j} \<in> ranking r (G \<setminus> X) \<pi>) \<in> A
    \<longleftrightarrow> (\<exists>i\<in>{i. {i,j} \<in> G \<setminus> X}. i \<notin> Vs M' \<and> Y i \<in> A \<and>
          (\<forall>i'\<in>{i. {i,j} \<in> G \<setminus> X}. i' \<notin> Vs M' \<longrightarrow> Y i \<le> Y i'))"
  (is "j \<in> Vs ?M \<and> Y (THE i. {i,j} \<in> ?M) \<in> A \<longleftrightarrow> ?F")
proof
  assume j_matched: "j \<in> Vs ?M \<and> Y (THE i. {i,j} \<in> ?M) \<in> A"
  let ?i = "min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X} r"

  from \<pi>_decomp have "?M = ranking' r (G \<setminus> X) M' (j#\<pi>'')"
    unfolding M'_def
    by (simp add: ranking_append)

  from \<pi>_decomp \<open>j \<in> R\<close> perm have "j \<notin> Vs M'"
    unfolding M'_def r_def
    by (intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI_remove_vertices)
       (auto dest: permutations_of_setD remove_vertices_subgraph')

  have neighbor_ex: "\<exists>i\<in>{i. {i,j} \<in> G \<setminus> X}. i \<notin> Vs M'" (is "?Ex")
  proof (rule ccontr)
    assume "\<not> ?Ex"

    then have step_unchanged: "step r (G \<setminus> X) M' j = M'"
      by (auto simp: step_def)

    with \<pi>_decomp have M: "?M = ranking' r (G \<setminus> X) M' \<pi>''"
      unfolding ranking'_def M'_def
      by simp

    from \<pi>_decomp \<open>j \<in> R\<close> \<open>j \<notin> Vs M'\<close> perm step_unchanged have "j \<notin> Vs ?M"
      by (subst M, intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI_remove_vertices)
         (auto dest: permutations_of_setD remove_vertices_subgraph' simp: r_def)
    
    with j_matched show False
      by blast
  qed

  with \<open>j \<notin> Vs M'\<close> have step_eq: "step r (G \<setminus> X) M' j = insert {?i, j} M'"
    by (auto simp add: step_def)

  from neighbor_ex \<open>j \<in> R\<close> bipartite_graph have i_unmatched: "?i \<in> {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"
    by (intro min_if_finite preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] finite_unmatched_neighbors)
       (auto simp: r_def intro: preorder_on_imp_preorder_on' dest: bipartite_edgeD remove_vertices_subgraph' edges_are_Vs remove_vertices_not_vs')

  from neighbor_ex \<open>j \<in> R\<close> bipartite_graph have i_min: 
    "\<not>(\<exists>i'\<in>{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}. (i',?i) \<in> r \<and> (?i,i') \<notin> r)"
    by (intro min_if_finite preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] finite_unmatched_neighbors)
       (auto simp: r_def intro: preorder_on_imp_preorder_on' dest: bipartite_edgeD remove_vertices_subgraph' edges_are_Vs remove_vertices_not_vs')

  have the_i: "(THE i. {i,j} \<in> ?M) = ?i"
  proof (intro the_match matching_ranking, goal_cases)
    case 4
    from \<pi>_decomp step_eq show ?case
      by (auto simp add: ranking_append ranking_Cons M'_def intro: ranking_mono)
  qed (use finite_vs in \<open>auto simp: r_def\<close>)

  show ?F
  proof (intro bexI[of _ ?i] conjI ballI impI, goal_cases)
    case (3 i')
    show ?case
    proof (rule ccontr, simp add: not_le)
      assume "Y i' < Y ?i"
      with 3 i_unmatched \<open>j \<in> R\<close> have "(i',?i) \<in> r \<and> (?i,i') \<notin> r"
        unfolding r_def linorder_from_keys_def
        by (auto dest: neighbors_right_subset_left_remove_vertices)

      with 3 i_min show False
        by blast
    qed
  qed (use i_unmatched j_matched in \<open>simp_all add: the_i\<close>)
next
  assume eligible_neighbor: ?F
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"

  from eligible_neighbor obtain i where 
    i_eligible: "i \<notin> Vs M'" "{i,j} \<in> G \<setminus> X" and
    Y_i: "Y i \<in> A" and
    i_min_on_r: "\<forall>i'\<in>?ns. Y i \<le> Y i'"
    by auto

  from \<pi>_decomp have "?M = ranking' r (G \<setminus> X) M' (j#\<pi>'')"
    unfolding ranking'_def M'_def
    by simp

  from \<pi>_decomp \<open>j \<in> R\<close> perm have j_unmatched_before: "j \<notin> Vs M'"
    unfolding M'_def r_def
    by (intro unmatched_R_in_ranking_if ballI preorder_on_neighborsI_remove_vertices)
       (auto dest: permutations_of_setD remove_vertices_subgraph')

  let ?min = "min_on_rel ?ns r"

  from j_unmatched_before i_eligible have step_eq: "step r (G \<setminus> X) M' j = insert {?min, j} M'"
    unfolding step_def
    by auto

  with finite_vs perm \<pi>_decomp \<open>j \<in> R\<close> have the_i_step: "(THE i. {i,j} \<in> step r (G \<setminus> X) M' j) = ?min"
    unfolding M'_def
    by (intro the_match matching_step matching_ranking ballI preorder_on_neighborsI_remove_vertices)
       (auto simp: r_def dest: permutations_of_setD)

  from \<open>j \<in> R\<close> bipartite_graph i_eligible have min_unmatched: "?min \<in> {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"
    unfolding r_def
    by (intro min_if_finite preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] preorder_on_imp_preorder_on' finite_unmatched_neighbors)
       (auto dest: bipartite_edgeD neighbors_right_subset_left_remove_vertices remove_vertices_subgraph')

  from \<open>j \<in> R\<close> bipartite_graph i_eligible have min_is_min: "\<not>(\<exists>x \<in> ?ns. (x,?min) \<in> r \<and> (?min, x) \<notin> r)"
    unfolding r_def
    by (intro min_if_finite preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] preorder_on_imp_preorder_on' finite_unmatched_neighbors)
       (auto dest: bipartite_edgeD neighbors_right_subset_left_remove_vertices remove_vertices_subgraph')

  have Y_min: "Y ?min = Y i"
  proof (rule ccontr)
    assume "Y ?min \<noteq> Y i"
    then consider "Y ?min < Y i" | "Y i < Y ?min"
      by linarith

    then show False
    proof cases
      case 1
      with min_unmatched i_min_on_r show ?thesis
        by auto
    next
      case 2
      with \<open>{i,j} \<in> G \<setminus> X\<close> \<open>j \<in> R\<close> bipartite_graph min_unmatched have "(i, ?min) \<in> r" "(?min, i) \<notin> r"
        unfolding r_def linorder_from_keys_def
        by (auto dest: bipartite_edgeD remove_vertices_subgraph' neighbors_right_subset_left_remove_vertices)

      with min_is_min i_eligible show ?thesis
        by blast
    qed
  qed

  show "j \<in> Vs ?M \<and> Y (THE i. {i,j} \<in> ?M) \<in> A"
  proof (intro conjI, goal_cases)
    case 1
    from \<pi>_decomp step_eq show ?case
      unfolding M'_def
      by (auto simp: ranking_append ranking_Cons vs_insert intro: ranking_mono_vs)
  next
    case 2
    from finite_vs perm \<pi>_decomp step_eq \<open>j \<in> R\<close> have "(THE i. {i,j} \<in> ranking r (G \<setminus> X) \<pi>) = ?min"
    unfolding M'_def
    by (intro the_match matching_step matching_ranking ballI preorder_on_neighborsI_remove_vertices)
       (auto intro: ranking_mono dest: permutations_of_setD simp: r_def ranking_append ranking_Cons)

  with Y_min Y_i show ?case
    by simp
  qed
qed

lemma dual_component_online_in_sets:
  assumes "j \<in> R"
  assumes "A \<in> sets (borel::real measure)"
  shows  "{Y \<in> space (Pi\<^sub>M (L - X) (\<lambda>i. uniform_measure lborel {0..1})). j \<in> Vs (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) \<and> 
    Y (THE l. {l, j} \<in> ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) \<in> A} \<in> sets (Pi\<^sub>M (L - X) (\<lambda>i. uniform_measure lborel {0..1}))"
proof -
  from \<open>j \<in> R\<close> perm obtain pre suff where \<pi>_decomp: "\<pi> = pre @ j # suff" "j \<notin> set pre" "j \<notin> set suff"
    by (metis permutations_of_setD split_list_distinct)

  with set_\<pi> have set_pre: "set pre \<subseteq> R"
    by auto

  show ?thesis
  proof (intro predE, subst online_matched_with_borel_iff[OF assms \<pi>_decomp], intro pred_intros_finite pred_intros_logic, goal_cases)
    case (2 i)
    with set_pre show ?case
      by measurable
  next
    case (3 i)
    with \<open>j \<in> R\<close> have "i \<in> L - X"
      by (auto dest: neighbors_right_subset_left_remove_vertices)

    with \<open>A \<in> sets borel\<close> show ?case
      by measurable
  next
    case (5 i i')
    with set_pre show ?case
      by measurable
  next
    case (6 i i')
    with \<open>j \<in> R\<close> have "i \<in> L - X" "i' \<in> L - X"
      by (auto dest: neighbors_right_subset_left_remove_vertices)

    then show ?case
      by measurable
  qed (intro remove_vertices_subgraph finite_neighbors)+
qed

lemma dual_component_online_borel_measurable:
  assumes "j \<in> R"
  shows "(\<lambda>Y. Y (THE l. {l, j} \<in> ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)) \<in> borel_measurable (restrict_space (\<Pi>\<^sub>M i \<in> L - X. U) {Y. j \<in> Vs (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)})"
proof (rule measurableI, goal_cases)
  case (2 A)
  show ?case
  proof (simp add: space_restrict_space sets_restrict_space image_def vimage_def Int_def,
      rule bexI[of _ "{Y \<in> space (\<Pi>\<^sub>M i \<in> L - X. U). j \<in> Vs (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) \<and> Y (THE l. {l,j} \<in> ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) \<in> A}"], goal_cases)
    case 2
    from \<open>j \<in> R\<close> \<open>A \<in> sets borel\<close> show ?case
      by (rule dual_component_online_in_sets)
  qed blast
qed simp

lemma measurable_dual_component_remove_vertices[measurable]:
  assumes "k < n"
  assumes "k < card L \<Longrightarrow> from_nat_into L k \<notin> X"
  shows "(\<lambda>Y. dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) $ k) \<in> borel_measurable (\<Pi>\<^sub>M i \<in> L - X. U)"
  unfolding dual_sol_def
proof (subst index_vec[OF \<open>k < n\<close>], subst measurable_If_restrict_space_iff, goal_cases)
  case 2
  then show ?case
  proof (rule conjI, subst measurable_If_restrict_space_iff; (intro conjI | simp), goal_cases)
    case 1
    show ?case
    proof (auto, rule measurable_restrict_space1, goal_cases)
      case 1
      show ?case
        by measurable (use \<open>k < card L\<close> assms in \<open>auto intro: from_nat_into simp: Vs_enum_inv_from_nat_into_L\<close>)
    qed
  next
    case 2
    show ?case
      by (simp, intro impI borel_measurable_divide borel_measurable_const borel_measurable_diff
          measurable_compose[OF dual_component_online_borel_measurable])
         (use \<open>k < n\<close> in \<open>auto elim: Vs_enum_inv_rightE\<close>)
  qed
qed measurable

lemmas measurable_dual_component = measurable_dual_component_remove_vertices[where X = "{}", simplified]

lemma measurable_dual_component_split_dim:
  assumes "i \<in> L"
  assumes "j < n"
  shows "(\<lambda>(y,Y). dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ j) \<in> borel_measurable (U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
  using measurable_compose[OF measurable_add_dim' measurable_dual_component] assms
  by (auto simp: case_prod_beta)

lemma measurable_dual_component_fun_upd:
  assumes "i \<in> L"
  assumes "Y \<in> space (Pi\<^sub>M (L - {i}) (\<lambda>i. U))"
  assumes "k < n"
  shows "(\<lambda>y. dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ k) \<in> borel_measurable U"
  by (rule measurable_compose[OF _ measurable_dual_component])
     (use assms in measurable)

lemma measurable_y\<^sub>c[measurable]: "j \<in> R \<Longrightarrow> (\<lambda>Y. y\<^sub>c Y \<pi> i j) \<in> borel_measurable (Pi\<^sub>M (L - {i}) (\<lambda>i. U))"
proof (unfold y\<^sub>c_def, subst measurable_If_restrict_space_iff, subst ranking_Restr_to_vertices[symmetric], goal_cases)
  case 2
  then show ?case
    by (subst linorder_from_keys_Restr) measurable
next
  case 3
  have "set \<pi> \<subseteq> R"
    by simp

  then have *: "(\<lambda>Y. Y (THE i'. {i', j} \<in> ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)) =
    (\<lambda>Y. Y (THE i'. {i',j} \<in> ranking (linorder_from_keys (L - {i}) Y) (G \<setminus> {i}) \<pi>))"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: preorder_on_imp_preorder_on' simp: linorder_from_keys_Restr)

  from \<open>set \<pi> \<subseteq> R\<close> have **: "restrict_space (Pi\<^sub>M (L - {i}) (\<lambda>i. U)) {Y. j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)} =
    restrict_space (Pi\<^sub>M (L - {i}) (\<lambda>i. U)) {Y. j \<in> Vs (ranking (linorder_from_keys (L - {i}) Y) (G \<setminus> {i}) \<pi>)}"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: preorder_on_imp_preorder_on' simp: linorder_from_keys_Restr)

  show ?case
    by (intro conjI, (subst * **)+, rule dual_component_online_borel_measurable)
       (simp_all add: \<open>j \<in> R\<close>)
qed auto

lemma dual_sol_funcset:
  assumes Y_nonneg: "\<And>i. i \<in> L - X \<Longrightarrow> 0 \<le> Y i"
  assumes Y_less_eq_One: "\<And>i. i \<in> L - X \<Longrightarrow> Y i \<le> 1"
  shows "($) (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
proof (intro funcsetI)
  fix i
  assume "i \<in> {..<n}"
  then have "i < n"
    by blast

  let ?ranking = "ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>"

  have "?ranking \<subseteq> G \<setminus> X"
    by (intro Ranking_Order.ranking_subgraph) auto

  then have matched_not_X: "j \<in> Vs ?ranking \<Longrightarrow> j \<notin> X" for j
    by (auto dest!: Vs_subset dest: remove_vertices_not_vs')

  from \<open>i < n\<close> show "dual_sol Y ?ranking $ i \<in> {0..1 / F}"
  proof (cases rule: i_cases)
    case 1
    with \<open>i < n\<close> show ?thesis
      unfolding dual_sol_def
      by (auto intro: g_nonnegI g_less_eq_OneI assms dest: matched_not_X elim: Vs_enum_inv_leftE)
  next
    case 2
    with \<open>i < n\<close> have "Vs_enum_inv i \<in> Vs ?ranking \<Longrightarrow> (THE i'. {i', Vs_enum_inv i} \<in> ?ranking) \<in> L" 
      "Vs_enum_inv i \<in> Vs ?ranking \<Longrightarrow>{(THE i'. {i', Vs_enum_inv i} \<in> ?ranking), Vs_enum_inv i} \<in> ?ranking"
      by (auto intro!: the_ranking_match_left dest: remove_vertices_subgraph' elim: Vs_enum_inv_rightE)
      
    with 2 \<open>i < n\<close> show ?thesis
      unfolding dual_sol_def
      by (auto intro: g_nonnegI g_less_eq_OneI assms dest: matched_not_X remove_vertices_subgraph' edges_are_Vs)
  qed
qed

lemma dual_sol_funcset_if_funcset:
  shows "Y \<in> (L - X) \<rightarrow> {0..1} \<Longrightarrow> ($) (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
  by (intro dual_sol_funcset) auto

lemma AE_dual_sol_funcset:
  shows "AE Y in \<Pi>\<^sub>M i \<in> L - X. U. ($) (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}" 
  using AE_PiM_subset_L_U_funcset[OF Diff_subset]
  by eventually_elim
     (auto dest: dual_sol_funcset_if_funcset)

lemma AE_dual_sol_split_dim_funcset:
  shows "AE (y, Y) in U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U). ($) (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
  using AE_split_dim_funcset
  by eventually_elim
     (auto dest: dual_sol_funcset_if_funcset[where X = "{}", simplified])

lemma AE_dual_sol_U_funcset:
  assumes "Y \<in> L - {i} \<rightarrow> {0..1}"
  shows "AE y in U. ($) (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
  using assms
  by (intro eventually_mono[OF AE_U_in_range] dual_sol_funcset_if_funcset[where X = "{}", simplified] funcset_update)

lemma integrable_g[simp]: "integrable U g"
proof (intro integrableI_real_bounded, goal_cases)
  case 2
  from AE_U_in_range show ?case
    by eventually_elim
       (auto intro: g_nonnegI)
  case 3
  have "\<integral>\<^sup>+ y. g y \<partial>U \<le> 1"
    by (intro component_prob_space.nn_integral_le_const eventually_mono[OF AE_U_in_range])
       (auto intro: g_less_eq_OneI)
  then show ?case
    by (simp add: order_le_less_trans)
qed simp
  
lemma integrable_dual_component_remove_vertices:
  assumes "i < n"
  assumes "i < card L \<Longrightarrow> from_nat_into L i \<notin> X"
  shows "integrable (\<Pi>\<^sub>M i \<in> L - X. U) (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) $ i)"
  using assms
proof (intro integrableI_nonneg measurable_dual_component, goal_cases)
  case 2
  show ?case
    by (rule eventually_mono[OF AE_dual_sol_funcset], use 2 in auto)
next
  case 3
  have "\<integral>\<^sup>+ Y. ennreal (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) $ i) \<partial>\<Pi>\<^sub>M i \<in> L - X. U \<le> 1/F"
    by (intro subprob_space.nn_integral_le_const prob_space_imp_subprob_space prob_space_PiM_U eventually_mono[OF AE_dual_sol_funcset])
       (use 3 in auto)

  then show ?case
    by (simp add: order_le_less_trans)
qed measurable

lemmas integrable_dual_component = integrable_dual_component_remove_vertices[where X = "{}", simplified]

lemma integrable_dual_component_split_dim:
  assumes "i \<in> L"
  assumes "j < n"
  shows "integrable (U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U)) (\<lambda>(y,Y). dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ j)"
  using assms
proof (intro integrableI_nonneg measurable_dual_component_split_dim, goal_cases)
  case 3
  show ?case
    by (rule eventually_mono[OF AE_dual_sol_split_dim_funcset], use 3 in auto)
next
  case 4
  interpret split_dim_prob_space: prob_space "(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
    by (intro prob_space_pair prob_space_PiM) blast+

  have "\<integral>\<^sup>+ (y,Y). ennreal (dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ j) \<partial>(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U)) \<le> 1/F"
    by (intro split_dim_prob_space.nn_integral_le_const eventually_mono[OF AE_dual_sol_split_dim_funcset])
       (use 4 in auto)

  then show ?case
    by (subst case_prod_beta, subst split_comp_eq)
       (simp add: order_le_less_trans)
qed

lemma integrable_dual_component_U:
  assumes "Y \<in> space (\<Pi>\<^sub>M i \<in> L - {i}. U)"
  assumes Y_funcset: "Y \<in> L - {i} \<rightarrow> {0..1}"
  assumes "i \<in> L"
  assumes "k < n"
  shows "integrable U (\<lambda>y. dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ k)"
proof (intro integrableI_real_bounded measurable_dual_component_fun_upd, goal_cases)
  case 4
  from Y_funcset \<open>k < n\<close> show ?case
    by (auto intro!: eventually_mono[OF AE_dual_sol_U_funcset])
next
  case 5
  from Y_funcset \<open>k < n\<close> have "\<integral>\<^sup>+y. dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ k \<partial>U \<le> 1/F"
    by (auto intro!: subprob_space.nn_integral_le_const prob_space_imp_subprob_space eventually_mono[OF AE_dual_sol_U_funcset])

  then show ?case
    by (simp add: order_le_less_trans)
qed (use assms in auto)

lemma integrable_integral_bound_but_i:
  assumes "j \<in> R"
  shows "integrable (Pi\<^sub>M (L - {i}) (\<lambda>i. U)) (\<lambda>Y. \<integral>y. g y * indicat_real {0..<y\<^sub>c Y \<pi> i j} y \<partial>U + 1 - g (y\<^sub>c Y \<pi> i j))"
proof (intro Bochner_Integration.integrable_add Bochner_Integration.integrable_diff integrableI_real_bounded component_prob_space.borel_measurable_lebesgue_integral, goal_cases)
  case 1
  then show ?case
  proof (subst split_comp_eq[symmetric],
      intro borel_measurable_times measurable_compose[where f = snd and g = g and N = U] measurable_snd, goal_cases)
    case 2
    show ?case
      unfolding atLeastLessThan_def atLeast_def lessThan_def
    proof (intro borel_measurable_indicator' predE pred_intros_logic pred_const_le[where N = U] measurable_snd, goal_cases)
      case 2
      from \<open>j \<in> R\<close> show ?case
      proof (intro borel_measurable_pred_less, goal_cases)
        case 2
        from \<open>j \<in> R\<close> show ?case
          by measurable
      qed simp
    qed simp
  qed (use g_borel in auto)
next
  case 2
  then show ?case
    by (intro eventually_mono[OF AE_PiM_subset_L_U_funcset[OF Diff_subset]] integral_nonneg_AE eventually_mono[OF AE_U_in_range])
       (auto intro: mult_nonneg_nonneg g_nonnegI)
next
  case 3
  have "\<integral>\<^sup>+ Y. ennreal (\<integral>y. g y * indicator {0..<y\<^sub>c Y \<pi> i j} y \<partial>U) \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U) \<le> 1"
    by (auto intro!: subprob_space.nn_integral_le_const prob_space_imp_subprob_space prob_space_PiM_U 
                     eventually_mono[OF AE_PiM_subset_L_U_funcset] integral_real_bounded 
                     eventually_mono[OF AE_U_in_range] mult_le_one g_less_eq_OneI component_prob_space.prob_space_axioms)

  then show ?case
    by (simp add: order_le_less_trans)
next
  case 8
  from assms show ?case
    by (auto intro!: g_nonnegI eventually_mono[OF AE_PiM_subset_L_U_funcset] dest: y\<^sub>c_bounded)
next
  case 9
  
  from assms have "\<integral>\<^sup>+ x. g (y\<^sub>c x \<pi> i j) \<partial>Pi\<^sub>M (L - {i}) (\<lambda>i. U) \<le> 1"
    by (auto intro!: subprob_space.nn_integral_le_const prob_space_imp_subprob_space prob_space_PiM_U 
                     eventually_mono[OF AE_PiM_subset_L_U_funcset] g_less_eq_OneI dest: y\<^sub>c_bounded)

  then show ?case
    by (simp add: order_le_less_trans)
qed (use \<open>j \<in> R\<close> in \<open>simp_all\<close>)

lemma linorder_on_linorder_from_keys_insert:
  assumes linorder: "linorder_on A (linorder_from_keys A f)"
  assumes "y \<notin> f ` A"
  assumes "a \<notin> A"
  shows "linorder_on (insert a A) (linorder_from_keys (insert a A) (f(a:=y)))"
proof -
  from \<open>a \<notin> A\<close> have linorder_from_insert: "linorder_from_keys (insert a A) (f(a:=y)) = linorder_from_keys A f \<union> {(a,a)} \<union> {(a,b) | b. b \<in> A \<and> y \<le> f b} \<union> {(b,a) | b. b \<in> A \<and> f b \<le> y}"
    unfolding linorder_from_keys_def
    by (auto split: if_splits)

  show "linorder_on (insert a A) (linorder_from_keys (insert a A) (f(a:=y)))"
    unfolding linorder_on_def
  proof (intro conjI, goal_cases)
    case 1
    with linorder show ?case
      by (subst linorder_from_insert)
         (auto simp: linorder_on_def refl_on_def)
  next
    case 2
    with linorder \<open>a \<notin> A\<close> \<open>y \<notin> f ` A\<close> show ?case
      by (subst linorder_from_insert)
         (auto simp: linorder_on_def antisym_def dest: refl_on_domain)
  next
    case 3
    with linorder \<open>a \<notin> A\<close> \<open>y \<notin> f ` A\<close> show ?case
      by (subst linorder_from_insert, unfold trans_def)
         (auto simp: linorder_from_keys_def linorder_on_def)
  next
    case 4
    with linorder show ?case
      by (subst linorder_from_insert, unfold linorder_on_def total_on_def)
         auto
  qed
qed

lemma AE_linorder_on_linorder_from_keys_add_dim:
  assumes "i \<in> L"
  assumes "linorder_on (L - {i}) (linorder_from_keys (L - {i}) Y)"
  shows "AE y in U. linorder_on L (linorder_from_keys L (Y(i:=y)))"
proof (intro eventually_mono[OF almost_everywhere_avoid_countable[where A = "Y ` (L - {i})"]], goal_cases)
  case (2 y)
  with assms have linorder_insert: "linorder_on (insert i (L - {i})) (linorder_from_keys (insert i (L - {i})) (Y(i:=y)))"
    by (intro linorder_on_linorder_from_keys_insert) auto

  from \<open>i \<in> L\<close> have "insert i (L - {i}) = L"
    by blast

  with linorder_insert show ?case
    by simp
qed (use finite_L in \<open>auto intro: countable_finite\<close>)

lemma dual_expectation_feasible_edge:
  assumes "i \<in> L"
  assumes "j \<in> R"
  assumes "{i,j} \<in> G"

  shows "expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum i)) +
    expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum j)) \<ge> 1"
  (is "?Ei_plus_Ej \<ge> 1")
proof -
  from assms have [intro]: "Vs_enum i < n" "Vs_enum j < n"
    by (auto simp: Vs_enum_L Vs_enum_R intro: L_enum_less_n R_enum_less_n)

  from \<open>{i,j} \<in> G\<close> have "?Ei_plus_Ej = expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum i) +
    dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum j))" (is "_ = expectation ?i_plus_j")
    by (intro Bochner_Integration.integral_add[symmetric] integrable_dual_component)
       (auto dest: edges_are_Vs intro: Vs_enum_less_n)

  also from \<open>i \<in> L\<close> have "\<dots> = integral\<^sup>L (\<Pi>\<^sub>M i \<in> (insert i (L - {i})).  U) ?i_plus_j"
    by (simp add: insert_absorb)

  also have "\<dots> = integral\<^sup>L (distr (U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> (L - {i}). U))
    (Pi\<^sub>M (insert i (L - {i})) (\<lambda>_. U))
    (\<lambda>(y,Y). Y(i := y))) ?i_plus_j"
    by (intro arg_cong2[where f = "integral\<^sup>L"] distr_pair_PiM_eq_PiM[symmetric])
       auto

  also have "\<dots> = integral\<^sup>L (U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> (L - {i}). U)) (?i_plus_j \<circ> (\<lambda>(y,Y). Y(i := y)))"
    unfolding comp_def
  proof (intro integral_distr, goal_cases)
    case 1
    then show ?case
      by measurable
  next
    case 2
    from \<open>i \<in> L\<close> show ?case
      by (intro borel_measurable_add)
         (auto simp: insert_absorb intro: measurable_dual_component)
  qed

  also have "\<dots> = \<integral>Y. \<integral>y. ?i_plus_j (Y(i := y)) \<partial>U \<partial>(\<Pi>\<^sub>M i \<in> (L - {i}). U)"
  proof (subst pair_sigma_finite.integral_snd, goal_cases)
    case 2
    then show ?case
      by (subst split_comp_eq[symmetric], rule Bochner_Integration.integrable_add; subst split_comp_eq)
         (use \<open>i \<in> L\<close> in \<open>auto intro!: integrable_dual_component_split_dim\<close>)
  next
    case 3
    then show ?case
      by (rule arg_cong2[where f = "integral\<^sup>L"]) auto
  qed auto

  also have "\<dots> \<ge> \<integral>Y. \<integral>y. g y / F * indicator {0..<y\<^sub>c Y \<pi> i j} y \<partial>U + (1 - g (y\<^sub>c Y \<pi> i j)) / F \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U)" (is "_ \<ge> ?integral_bound1")
  proof (intro integral_mono_AE, goal_cases)
    case 1

    from \<open>j \<in> R\<close> show ?case
      by (auto simp flip: add_divide_distrib simp: add_diff_eq intro: integrable_integral_bound_but_i)
  next
    case 2
    show ?case
    proof (intro integrableI_real_bounded component_prob_space.borel_measurable_lebesgue_integral, goal_cases)
      case 1
      from \<open>i \<in> L\<close> \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> show ?case
        using measurable_dual_component_split_dim
        by measurable
    next
      case 2
      from \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> show ?case
        by (intro eventually_mono[OF AE_PiM_subset_L_U_funcset[OF Diff_subset]] integral_nonneg_AE eventually_mono[OF AE_U_in_range])
           (auto dest!: funcset_update dual_sol_funcset_if_funcset[where X = "{}", simplified] intro!: add_nonneg_nonneg)
    next
      case 3
      interpret L'_prob_space: prob_space "\<Pi>\<^sub>M i \<in> L - {i}. U"
        by (intro prob_space_PiM) blast

      have "\<integral>\<^sup>+Y. (component_prob_space.expectation (\<lambda>y. dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i +
                                              dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j)) 
            \<partial>Pi\<^sub>M (L - {i}) (\<lambda>i. U) \<le> \<integral>\<^sup>+_. 2/F \<partial>Pi\<^sub>M (L - {i}) (\<lambda>i. U)"
      proof (intro nn_integral_mono_AE eventually_mono[OF AE_PiM_subset_L_U_funcset[OF Diff_subset]], simp, 
             intro integral_real_bounded component_prob_space.nn_integral_le_const eventually_mono[OF AE_U_in_range], goal_cases)
        case (3 Y y)
        then have "($) (dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
          by (auto dest!: funcset_update dual_sol_funcset_if_funcset[where X = "{}", simplified])

        with \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> have "dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i \<le> 1/F"
          "dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j \<le> 1/F"
          by auto

        then show ?case
          by simp
      qed simp_all

      also have "\<dots> = 2/F"
        by (simp add: L'_prob_space.emeasure_space_1)

      finally show ?case
        by (simp add: order_le_less_trans)
    qed
  next
    case 3
    from finite_L have AE_Y_props: 
      "AE Y in PiM (L - {i}) (\<lambda>i. U). Y \<in> space (PiM (L - {i}) (\<lambda>i. U)) \<and> 
                                      Y \<in> L-{i} \<rightarrow> {0..1} \<and> 
                                      linorder_on (L - {i}) (linorder_from_keys (L - {i}) Y)"
      by (auto intro: AE_PiM_subset_L_U_funcset intro!: AE_distrD[OF _ almost_everywhere_linorder[where B = "L - {i}"]])
         (use measurable_linorder_from_keys_restrict in measurable)
    
    show ?case
    proof (rule eventually_mono[OF AE_Y_props])
      fix Y :: "'a \<Rightarrow> real"
      assume Y: "Y \<in> space (PiM (L - {i}) (\<lambda>i. U)) \<and> Y \<in> L-{i} \<rightarrow> {0..1} \<and> linorder_on (L - {i}) (linorder_from_keys (L - {i}) Y)"

      have integrable_offline_bound: "integrable U (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y)"
        by (auto intro!: integrable_divide intro: integrable_real_mult_indicator)

      have *: "(1 - g (y\<^sub>c Y \<pi> i j)) / F = component_prob_space.expectation (\<lambda>y. (1 - g (y\<^sub>c Y \<pi> i j)) / F)" for Y
        by (simp add: measure_def component_prob_space.emeasure_space_1)

      have "component_prob_space.expectation (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y) + (1 - g (y\<^sub>c Y \<pi> i j)) / F = 
      component_prob_space.expectation (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y + (1 - g (y\<^sub>c Y \<pi> i j)) / F)"
        by (subst *, intro Bochner_Integration.integral_add[symmetric] integrable_offline_bound, auto)

      also have "\<dots> \<le> component_prob_space.expectation (\<lambda>y. dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i +
                         dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j)"
      proof (intro integral_mono_AE Bochner_Integration.integrable_add integrable_offline_bound, goal_cases)
        case 2
        with \<open>i \<in> L\<close> \<open>Vs_enum i < n\<close> Y show ?case
          by (auto intro: integrable_dual_component_U)
      next
        case 3
        with \<open>i \<in> L\<close> \<open>Vs_enum j < n\<close> Y show ?case
          by (auto intro: integrable_dual_component_U)
      next
        case 4
        from Y \<open>i \<in> L\<close> have AE_y: "AE y in U. y \<in> {0..1} \<and> Y(i:=y) \<in> L \<rightarrow> {0..1} \<and> linorder_on L (linorder_from_keys L (Y(i := y)))"
          by (auto intro: AE_linorder_on_linorder_from_keys_add_dim eventually_mono[OF AE_U_in_range] AE_U_funcset)

        then show ?case
        proof (rule eventually_mono, goal_cases)
          case (1 y)
          note y_props = this
          then show ?case
          proof (intro add_mono, goal_cases)
            case 1
            then have *: "($) (dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
              by (intro dual_sol_funcset[where X = "{}", simplified])
                 (auto simp: Pi_iff)

            have "y < y\<^sub>c Y \<pi> i j \<Longrightarrow> g y / F \<le> dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i"
            proof -
              assume "y < y\<^sub>c Y \<pi> i j"
              with \<open>j \<in> R\<close> have "y < y\<^sub>c (Y(i:=y)) \<pi> i j"
                by (simp add: y\<^sub>c_fun_upd_eq)

              with y_props \<open>i \<in> L\<close> \<open>j \<in> R\<close> \<open>{i,j} \<in> G\<close> have "i \<in> Vs (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>)"
                by (auto intro: dominance)

              with \<open>Vs_enum i < n\<close> \<open>i \<in> L\<close> have "dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ Vs_enum i = g y / F"
                by (auto simp: dual_sol_def)
                   (metis L_enum_less_card Vs_enum_L)+

              then show ?thesis
                by auto
            qed
              
            with * show ?case
              by (auto simp: indicator_times_eq_if)
          next
            case 2
            with \<open>i \<in> L\<close> \<open>j \<in> R\<close> \<open>{i,j} \<in> G\<close> show ?case 
              by (subst y\<^sub>c_fun_upd_eq[where y = y, symmetric], auto intro!: monotonicity)
          qed
        qed
      qed simp

      finally show "component_prob_space.expectation (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y) + (1 - g (y\<^sub>c Y \<pi> i j)) / F
         \<le> component_prob_space.expectation (\<lambda>y. dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i 
                                  + dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j)"
        .
    qed
  qed

  finally have "?Ei_plus_Ej \<ge> ?integral_bound1" .

  have "?integral_bound1 = \<integral>Y. \<integral>y. g y * indicator {0..<y\<^sub>c Y \<pi> i j} y \<partial>U + 1 - g (y\<^sub>c Y \<pi> i j) \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U) / F "
    by (auto simp flip: add_divide_distrib simp: algebra_simps)

  also have "\<dots> \<ge> \<integral>Y. F \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U) / F" (is "_ \<ge> ?integral_bound2")
  proof (subst div_F_less_eq_cancel, intro integral_mono_AE, goal_cases)
    case 1
    show ?case
      by (auto intro: finite_measure.integrable_const prob_space.finite_measure prob_space_PiM_U)
  next
    case 2
    from \<open>j \<in> R\<close> show ?case
      by (auto intro: integrable_integral_bound_but_i)
  next
    case 3
    from \<open>j \<in> R\<close> show ?case
      by (auto intro!: eventually_mono[OF AE_PiM_subset_L_U_funcset] g_integral_bound dest: y\<^sub>c_bounded)
  qed

  finally have "?integral_bound1 \<ge> ?integral_bound2" .

  from F_gt_0 have "?integral_bound2 = 1"
    by (auto simp: measure_def)

  with \<open>?Ei_plus_Ej \<ge> ?integral_bound1\<close> \<open>?integral_bound1 \<ge> ?integral_bound2\<close> show ?thesis
    by linarith
qed


abbreviation "expected_dual \<equiv> vec n (\<lambda>i. expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i))"

lemma expected_dual_feasible: "incidence_matrix\<^sup>T *\<^sub>v expected_dual \<ge> 1\<^sub>v m"
  unfolding Matrix.less_eq_vec_def
proof (intro conjI allI impI, simp_all add: incidence_matrix_def)
  fix k assume "k < m"

  then obtain i j where ij: "{i,j} \<in> G" "from_nat_into G k = {i,j}" "i \<in> L" "j \<in> R"
    by (auto elim: from_nat_into_G_E)

  with bipartite_graph have index_neq: "Vs_enum i \<noteq> Vs_enum j"
    by (intro Vs_enum_neqI) (auto dest: edges_are_Vs)

  {
    fix l r
    assume "from_nat_into G k = {l,r}" "l \<in> L" "r \<in> R"

    with ij have "l = i" "r = j"
      by auto
  } note the_lr = this

  from ij have "1 \<le> expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ Vs_enum i) +
            expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ Vs_enum j)"
    by (intro dual_expectation_feasible_edge)

  also from index_neq have "\<dots> = (\<Sum>k\<in>{Vs_enum i, Vs_enum j}. expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ k))"
    by simp

  also from the_lr \<open>{i,j} \<in> G\<close> \<open>k < m\<close> have "\<dots> = vec n (\<lambda>i. of_bool (Vs_enum_inv i \<in> from_nat_into G k)) \<bullet> vec n (\<lambda>i. expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i))"
    unfolding incidence_matrix_def
    by (auto simp: scalar_prod_def sum.cong[OF index_set_Int_is_doubleton] elim!: from_nat_into_G_E)

  finally show "1 \<le> vec n (\<lambda>i. of_bool (Vs_enum_inv i \<in> from_nat_into G k)) \<bullet> vec n (\<lambda>i. expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i))"
    .
qed

lemma expected_dual_nonneg: "expected_dual \<ge> 0\<^sub>v n"
  unfolding Matrix.less_eq_vec_def
proof (intro conjI allI impI, simp_all, intro integral_ge_const integrable_dual_component)
  fix k
  assume "k < n"

  have "j \<in> Vs (ranking (linorder_from_keys L Y) G \<pi>) \<Longrightarrow> j \<in> R \<Longrightarrow> (THE l. {l, j} \<in> ranking (linorder_from_keys L Y) G \<pi>) \<in> L" for j Y
    by (auto intro!: the_ranking_match_left)

  with \<open>k < n\<close> show "AE Y in M\<^sub>Y. 0 \<le> dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ k"
    unfolding dual_sol_def
    by (intro eventually_mono[OF AE_Y_funcset])
       (auto intro!: g_nonnegI g_less_eq_OneI simp: Pi_iff elim: Vs_enum_inv_leftE Vs_enum_inv_rightE)
qed blast

theorem ranking_F_competitive:
  assumes "G \<noteq> {}"
  assumes "max_card_matching G M"

  shows "expectation (\<lambda>Y. card (ranking (linorder_from_keys L Y) G \<pi>)) / card M \<ge> F" (is "?EM / _ \<ge> _")
proof -
  from assms have "M \<noteq> {}" "finite M"
    by (auto dest: max_card_matching_non_empty max_card_matchingD finite_subset)
    
  then have "card M > 0"
    by auto

  from assms have max_card_bound: "card M \<le> 1\<^sub>v n \<bullet> expected_dual"
    by (auto intro: max_card_matching_bound_by_feasible_dual expected_dual_feasible expected_dual_nonneg)

  have "?EM = expectation (\<lambda>Y. 1\<^sub>v m \<bullet> primal_sol (ranking (linorder_from_keys L Y) G \<pi>))"
    by (subst primal_dot_One_card, rule ranking_subgraph)
        auto

  also have "\<dots> = expectation (\<lambda>Y. 1\<^sub>v n \<bullet> dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) * F)"
    by (intro Bochner_Integration.integral_cong refl primal_is_dual_times_F ranking_subgraph matching_ranking)
        auto

  also have "\<dots> = 1\<^sub>v n \<bullet> expected_dual * F" (is "?E = ?Edot1F")
  proof -
    from F_gt_0 have "?E = expectation (\<lambda>Y. \<Sum>i\<in>{0..<n}. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i) * F"
      by (auto simp: scalar_prod_def)

    also have "\<dots> = (\<Sum>i\<in>{0..<n}. expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i)) * F"
      by (auto intro!: Bochner_Integration.integral_sum intro: integrable_dual_component)

    also have "\<dots> = ?Edot1F"
      by (auto simp: scalar_prod_def)

    finally show ?thesis .
  qed

  finally have "?EM = ?Edot1F" .

  with F_gt_0 max_card_bound \<open>card M > 0\<close> show ?thesis
    by (auto intro: mult_imp_le_div_pos mult_left_mono simp: mult.commute)
qed

lemma expectation_ranking_eq_random_linorder:
  "expectation (\<lambda>Y. card (ranking (linorder_from_keys L Y) G \<pi>)) =
    prob_space.expectation (uniform_measure (count_space (Pow (L \<times> L))) (linorders_on L)) (\<lambda>r. card (ranking r G \<pi>))"
  (is "?EY = ?Er")
proof -
  from finite_L have "?EY = prob_space.expectation (distr (\<Pi>\<^sub>M i \<in> L. uniform_measure lborel {0..1::real}) (count_space (Pow (L \<times> L))) (linorder_from_keys L))
                              (\<lambda>r. card (ranking r G \<pi>))"
    by (intro integral_distr[symmetric]) 
       (use measurable_linorder_from_keys_restrict in measurable)

  also from finite_L have "\<dots> = prob_space.expectation (uniform_measure (count_space (Pow (L \<times> L))) (linorders_on L)) (\<lambda>r. card (ranking r G \<pi>))"
    by (auto simp: random_linorder_by_prios)

  finally show ?thesis .
qed

corollary ranking_F_competitive_random_linorder:
  assumes "G \<noteq> {}"
  assumes "max_card_matching G M"
  shows
    "prob_space.expectation (uniform_measure (count_space (Pow (L \<times> L))) (linorders_on L)) (\<lambda>r. card (ranking r G \<pi>)) / card M \<ge> F"
  using assms
  by (auto simp flip: expectation_ranking_eq_random_linorder intro: ranking_F_competitive)

end

theorem
  assumes "bipartite G L R"
  assumes "finite L" "finite R" "Vs G = L \<union> R"

  assumes "G \<noteq> {}"
  assumes "\<pi> \<in> permutations_of_set R"
  assumes "max_card_matching G M"

  shows ranking_competitive_ratio: 
    "prob_space.expectation (\<Pi>\<^sub>M i \<in> L. uniform_measure lborel {0..1::real}) (\<lambda>Y. card (ranking (linorder_from_keys L Y) G \<pi>)) / card M
      \<ge> 1 - exp(-1)" (is "?EY \<ge> _")

  and ranking_competitive_ratio_random_linorder:
    "prob_space.expectation (uniform_measure (count_space (Pow (L \<times> L))) (linorders_on L)) (\<lambda>r. card (ranking r G \<pi>)) / card M
      \<ge> 1 - exp(-1)" (is "?Er \<ge> _")
proof -
  from assms interpret wf_ranking_order_prob_exp: wf_ranking_order_prob L R G \<pi> "\<lambda>y. exp(y-1)" "1 - exp(-1)"
    by unfold_locales (auto intro: mono_onI simp: exp_minus_One_integral_indicator)

  from assms show "?EY \<ge> 1 - exp(-1)" "?Er \<ge> 1 - exp(-1)"
    by (auto intro: wf_ranking_order_prob_exp.ranking_F_competitive wf_ranking_order_prob_exp.ranking_F_competitive_random_linorder)
qed

end
