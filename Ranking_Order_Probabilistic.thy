theory Ranking_Order_Probabilistic
  imports
    Ranking_Order
    "Jordan_Normal_Form.Matrix"
    "Treaps.Random_List_Permutation"
begin

hide_const Finite_Cartesian_Product.vec Finite_Cartesian_Product.vec.vec_nth

lemma restrict_space_UNIV[simp]: "restrict_space M UNIV = M"
  unfolding restrict_space_def
  by (auto simp: measure_of_of_measure)

lemma borel_measurable_restrict_space_empty[simp,intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {banach,second_countable_topology}"
  shows "f \<in> borel_measurable (restrict_space M {})"
  by (auto intro: borel_measurable_integrable simp: integrable_restrict_space)

lemma total_preorder_on_linorder_from_keys[intro]: "total_preorder_on A (linorder_from_keys A f)"
  unfolding linorder_from_keys_def total_preorder_on_def preorder_on_def
  by (auto simp: refl_on_def trans_def total_on_def) 

lemma linorder_from_keys_in_total_preorders_on[intro]: "linorder_from_keys A f \<in> total_preorders_on A"
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

find_theorems almost_everywhere measurable
text \<open>Generalize @{thm measurable_linorder_from_keys_restrict} by Eberl from
 \<^term>\<open>count_space (Pow (A \<times> A))\<close> to \<^term>\<open>count_space (total_preorders_on A)\<close>. The original
  statement then also follows with @{thm measurable_count_space_extend}.}\<close>
lemma measurable_linorder_from_keys_restrict_preorders[measurable]:
  assumes fin: "finite A"
  shows "linorder_from_keys A \<in> Pi\<^sub>M A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (total_preorders_on A)"
  (is "_ : ?M \<rightarrow>\<^sub>M _")
  apply (subst measurable_count_space_eq2)
   apply (auto simp: fin)
proof -
  note fin[simp]
  fix r assume "r \<in> total_preorders_on A"
  then have "linorder_from_keys A -` {r} \<inter> space ?M =
    {f \<in> space ?M. \<forall>x\<in>A. \<forall>y\<in>A. (x,y) \<in> r \<longleftrightarrow> f x \<le> f y}"
    by (auto simp: linorder_from_keys_def total_preorder_on_def preorder_on_def set_eq_iff dest!: total_preorders_onD refl_on_domain)

  also have "\<dots> \<in> sets ?M"
    by measurable

  finally show "linorder_from_keys A -` {r} \<inter> space ?M \<in> sets ?M" .
qed

lemma measurable_add_dim'[measurable]:
  assumes "i \<in> L"
  shows "(\<lambda>(y, Y). Y(i := y)) \<in> M i \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) M \<rightarrow>\<^sub>M Pi\<^sub>M L M" (is "?f \<in> M i \<Otimes>\<^sub>M ?PiM' \<rightarrow>\<^sub>M ?PiM")
proof -
  have "(\<lambda>(Y,y). Y(i := y)) \<in> ?PiM' \<Otimes>\<^sub>M M i \<rightarrow>\<^sub>M Pi\<^sub>M (insert i (L - {i})) M"
    by (rule measurable_add_dim)

  with assms show ?thesis
    by (subst measurable_pair_swap_iff) (auto simp: insert_absorb)
qed

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

lemma AE_uniform_measure_in_set_mono:
  "A \<in> sets M \<Longrightarrow> A \<subseteq> B \<Longrightarrow> AE x in uniform_measure M A. x \<in> B" 
  by (auto intro: AE_uniform_measureI)

lemma AE_PiM_uniform_measure_component_in_set:
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> 0"
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> \<infinity>"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> B i"
  assumes "i \<in> I"
  shows "AE f in PiM I (\<lambda>i. uniform_measure (M i) (A i)). f i \<in> B i"
  using assms
  by (intro AE_PiM_component prob_space_uniform_measure AE_uniform_measure_in_set_mono)

lemma AE_PiM_uniform_measure_PiE_countable:
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> 0"
  assumes "\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) (A i) \<noteq> \<infinity>"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  assumes "countable I"
  shows "AE f in PiM I (\<lambda>i. uniform_measure (M i) (A i)). f \<in> Pi I A"
  using assms
  by (subst Pi_iff) (rule AE_ball_countable', intro AE_PiM_uniform_measure_component_in_set; auto)


locale wf_ranking_order_prob = wf_ranking_order +
  fixes \<pi> :: "('a::linorder) list"
  fixes g :: "real \<Rightarrow> real" and F :: real

  assumes perm: "\<pi> \<in> permutations_of_set R"

  assumes g_from_to: "g \<in> {0..1} \<rightarrow> {0..1}"
  assumes g_mono: "mono_on g {0..1}"
  assumes g_One: "g 1 = 1"
  assumes g_borel[measurable]: "g \<in> borel_measurable borel"

  assumes g_integral_bound: "0 \<le> \<theta> \<Longrightarrow> \<theta> \<le> 1 \<Longrightarrow> \<integral>y. g y * indicator {0..<\<theta>} y \<partial>uniform_measure lborel {0..1} + (1 - g \<theta>) \<ge> F"

  assumes F_gt_0: "0 < F"


begin

abbreviation "U \<equiv> uniform_measure lborel {0..1::real}"
abbreviation "Y_measure \<equiv> \<Pi>\<^sub>M i \<in> L. U"

sublocale U_prob_space: prob_space U
  by (auto intro: prob_space_uniform_measure)

lemmas U_prob_space.prob_space_axioms[intro]

sublocale prob_space Y_measure
  by (auto intro: prob_space_PiM)

lemma prob_space_PiM_U:
  "prob_space (PiM I (\<lambda>_. U))"
  by (auto intro: prob_space_PiM)

lemma emeasure_space_PiM_U:
  shows "emeasure (PiM I (\<lambda>_. U)) (space (PiM I (\<lambda>_. U))) = 1"
  by (intro prob_space.emeasure_space_1 prob_space_PiM_U)

lemma pair_sigma_finite_split_dim[intro]: "pair_sigma_finite U (Pi\<^sub>M (L - {i}) (\<lambda>i. U))"
  by (intro pair_sigma_finite.intro prob_space_imp_sigma_finite prob_space_PiM) blast+

lemma (in pair_sigma_finite) pair_sigma_finite_swap: "pair_sigma_finite M2 M1"
  by (simp add: M1.sigma_finite_measure_axioms M2.sigma_finite_measure_axioms pair_sigma_finite_def)

lemmas pair_sigma_finite_split_dim'[intro] = pair_sigma_finite.pair_sigma_finite_swap[OF pair_sigma_finite_split_dim]

definition "n \<equiv> card (Vs G)"
definition "m \<equiv> card G"

definition Vs_enum :: "'a \<Rightarrow> nat" where
  "Vs_enum x \<equiv> if x \<in> L then to_nat_on L x else to_nat_on R x + card L"

definition Vs_enum_inv :: "nat \<Rightarrow> 'a" where
  "Vs_enum_inv i \<equiv> if i < card L then from_nat_into L i else from_nat_into R (i - card L)"

abbreviation G_enum :: "'a set \<Rightarrow> nat" where
  "G_enum \<equiv> to_nat_on G"

definition primal_sol :: "'a graph \<Rightarrow> nat vec" where
  "primal_sol M \<equiv> vec m (\<lambda>i. of_bool (from_nat_into G i \<in> M))"

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

lemma n_sum: "n = card L + card R"
  using parts_minimal finite_L finite_R
  by (auto simp: card_Un_disjoint n_def)

lemma geq_L_less_n_less_R: "card L \<le> i \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto simp: n_sum)

lemma geq_L_less_n_less_R': "\<not> i < card L \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto intro: geq_L_less_n_less_R)

lemma Vs_cases: 
  assumes "x \<in> Vs G"
  obtains "x \<in> L \<and> x \<notin> R" | "x \<in> R \<and> x \<notin> L"
  using assms parts_minimal
  by auto

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
  using finite_L finite_R
  by (auto simp: countable_finite intro: to_nat_on_from_nat_into_less)

lemma
  shows L_enum_less_card: "l \<in> L \<Longrightarrow> to_nat_on L l < card L"
    and R_enum_less_card: "r \<in> R \<Longrightarrow> to_nat_on R r < card R"
  using finite_L finite_R
  by (auto intro: to_nat_on_less_card)

lemma
  shows L_enum_less_n: "l \<in> L \<Longrightarrow> to_nat_on L l < n"
    and R_enum_less_n: "r \<in> R \<Longrightarrow> to_nat_on R r + card L < n"
  by (auto simp: n_sum dest: L_enum_less_card R_enum_less_card)

lemma
  shows Vs_enum_L: "l \<in> L \<Longrightarrow> Vs_enum l = to_nat_on L l"
    and Vs_enum_inv_from_nat_into_L: "i < card L \<Longrightarrow> Vs_enum_inv i = from_nat_into L i"
  unfolding Vs_enum_def Vs_enum_inv_def
  by auto

lemma
  shows Vs_enum_R: "r \<in> R \<Longrightarrow> Vs_enum r = to_nat_on R r + card L"
    and "card L \<le> i \<Longrightarrow> Vs_enum_inv i = from_nat_into R (i - card L)"
  unfolding Vs_enum_def Vs_enum_inv_def
  by auto

lemma Vs_enum_less_n: "x \<in> Vs G \<Longrightarrow> Vs_enum x < n"
  by (auto elim!: Vs_cases simp: Vs_enum_L Vs_enum_R intro: L_enum_less_n R_enum_less_n)

lemma
  shows Vs_inv_enum[simp]: "x \<in> Vs G \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
    and Vs_enum_inv[simp]: "i < n \<Longrightarrow> Vs_enum (Vs_enum_inv i) = i"
  using finite_L finite_R
  by (auto elim!: Vs_cases simp: Vs_enum_inv_def Vs_enum_def n_sum dest: L_enum_less_card intro!: from_nat_into)

lemma
  shows Vs_inv_enum_L[simp]: "i \<in> L \<Longrightarrow> Vs_enum_inv (Vs_enum i) = i"
    and Vs_inv_enum_R[simp]: "j \<in> R \<Longrightarrow> Vs_enum_inv (Vs_enum j) = j"
  by (simp_all add: parts_minimal)

lemma Vs_enum_inv_leftE:
  assumes "i < card L"
  obtains j where "j \<in> L" "Vs_enum_inv i = j"
  using assms
  by (metis Vs_enum_inv_def card.empty from_nat_into not_less_zero)

lemma Vs_enum_inv_rightE:
  assumes "i < n"
  assumes "\<not> i < card L"
  obtains j where "j \<in> R" "Vs_enum_inv i = j"
  using assms
  by (metis Vs_enum_inv_def add.right_neutral card.empty from_nat_into n_sum)lemma g_nonnegI: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> g x"
  using g_from_to
  by auto

lemma g_less_eq_OneI: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> g x \<le> 1"
  using g_from_to
  by auto

lemma div_F_nonneg[simp]: "0 \<le> x / F \<longleftrightarrow> 0 \<le> x"
  using F_gt_0
  by (simp add: zero_le_divide_iff)

lemma div_F_less_eq_cancel[simp]: "x / F \<le> y / F \<longleftrightarrow> x \<le> y"
  using F_gt_0
  by (simp add: divide_le_cancel)

lemma preorder_on_neighbors_linorder_from_keys[intro]:
  assumes "H \<subseteq> G"
  assumes "j \<in> R"
  shows "total_preorder_on' {i. {i,j} \<in> H} (linorder_from_keys L Y)"
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
       (auto intro: total_preorder_on_imp_total_preorder_on')
    
  also have "\<dots> = ranking (linorder_from_keys (L - {i}) (Y)) (G \<setminus> {i}) js" (is "_ = ?M")
    by (simp add: linorder_from_keys_Restr linorder_from_keys_update_eq)

  finally have "?L = ?M" .

  from assms have "?R = ranking (Restr (linorder_from_keys L Y) (L - {i})) (G \<setminus> {i}) js"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: total_preorder_on_imp_total_preorder_on')

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

\<comment> \<open>Lemma 2 from DJK\<close>
lemma dominance:
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
         (auto dest: permutations_of_setD linorder_on_imp_preorder_on)

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

    from perm \<pi>_decomp \<open>i \<in> L\<close> have "L - {i} - Vs ?ranking_pre' \<subseteq> L - Vs ?ranking_pre"
      by (intro monotonicity_order_ranking ballI preorder_on_neighborsI)
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

  from perm edges \<open>{i,j} \<in> G\<close> \<open>i \<in> L\<close> \<open>j \<in> R\<close> have "(i',i'') \<in> linorder_from_keys L Y"
    by (intro monotonicity_order_matched_matched) (auto dest: permutations_of_setD)

  then have "Y i' \<le> Y i''"
    unfolding linorder_from_keys_def
    by simp
  
  with True j_matched index_j i_left g_mono \<open>{i,j} \<in> G\<close> \<open>Y \<in> L \<rightarrow> {0..1}\<close> show ?thesis
    unfolding y\<^sub>c_def dual_sol_def
    by (auto simp: the_i' the_i'' dest!: edges_are_Vs intro!: mono_onD[where f = g])
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

    with True j_unmatched' index_j F_gt_0 \<open>{i,j} \<in> G\<close> \<open>Y \<in> L \<rightarrow> {0..1}\<close>show ?thesis
      unfolding y\<^sub>c_def dual_sol_def
      by (auto simp: g_One dest!: edges_are_Vs intro: divide_nonneg_pos intro!: g_less_eq_OneI)
  next
    case False
    
    with j_unmatched' index_j F_gt_0 \<open>{i,j} \<in> G\<close>show ?thesis
      unfolding y\<^sub>c_def dual_sol_def
      by (auto simp: g_One dest: edges_are_Vs intro: divide_nonneg_pos)
  qed
qed

lemma ranking_measurable':
  assumes "H \<subseteq> G"
  assumes "set js \<subseteq> R"
  shows "(\<lambda>Y. ranking (linorder_from_keys L Y) H js) \<in> Y_measure \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys L" _ "count_space (total_preorders_on L)"], goal_cases)
  case 1
  from finite_L show ?case
    by measurable
next
  case 2
  from finite_subsets \<open>set js \<subseteq> R\<close> \<open>H \<subseteq> G\<close> show ?case
    by (subst measurable_count_space_eq2)
       (auto dest: ranking_subgraph' total_preorders_onD)
qed

lemma ranking_measurable_remove_vertices:
  assumes "set js \<subseteq> R"
  shows "(\<lambda>Y. ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) js) \<in> (\<Pi>\<^sub>M i \<in> L - X. U) \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys (L - X)" _ "count_space (total_preorders_on (L - X))"], goal_cases)
  case 1
  from finite_L have "finite (L - X)" by blast
  then show ?case
    by measurable
next
  case 2
  from \<open>set js \<subseteq> R\<close> have "total_preorder_on (L - X) r \<Longrightarrow> ranking r (G \<setminus> X) js \<subseteq> G \<setminus> X" for r
    by (intro Ranking_Order.ranking_subgraph) auto

  with finite_subsets finite_vs show ?case
    by (auto dest: total_preorders_onD remove_vertices_subgraph')
qed

lemmas ranking_measurable = ranking_measurable'[OF subset_refl]

lemma ranking_measurable_fun_upd:
  assumes "i \<in> L"
  assumes "set js \<subseteq> R"
  assumes "Y \<in> space (Pi\<^sub>M (L - {i}) (\<lambda>_. U))"
  shows "(\<lambda>y. ranking (linorder_from_keys L (Y(i:=y))) G js) \<in> U \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "\<lambda>y. linorder_from_keys L (Y(i:=y))" _ "count_space (total_preorders_on L)"], goal_cases)
  case 1
  from finite_L assms show ?case
    by (measurable, simp add: space_PiM)
next
  case 2
  with \<open>set js \<subseteq> R\<close> show ?case
    by (auto dest: total_preorders_onD ranking_subgraph[OF subset_refl])
qed

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
  let ?i = "determ_min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X} r"

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
    by (intro min_if_finite total_preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] finite_unmatched_neighbors)
       (auto simp: r_def intro: total_preorder_on_imp_total_preorder_on' dest: bipartite_edgeD remove_vertices_subgraph' edges_are_Vs remove_vertices_not_vs')

  from neighbor_ex \<open>j \<in> R\<close> bipartite_graph have i_min: 
    "\<forall>i'\<in>{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}. (?i,i') \<in> r"
    by (intro ballI min_on_rel_least total_preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] finite_unmatched_neighbors)
       (auto simp: r_def intro: total_preorder_on_imp_total_preorder_on' dest: bipartite_edgeD remove_vertices_subgraph' edges_are_Vs remove_vertices_not_vs')

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

  let ?min = "determ_min_on_rel ?ns r"

  from j_unmatched_before i_eligible have step_eq: "step r (G \<setminus> X) M' j = insert {?min, j} M'"
    unfolding step_def
    by auto

  with finite_vs perm \<pi>_decomp \<open>j \<in> R\<close> have the_i_step: "(THE i. {i,j} \<in> step r (G \<setminus> X) M' j) = ?min"
    unfolding M'_def
    by (intro the_match matching_step matching_ranking ballI preorder_on_neighborsI_remove_vertices)
       (auto simp: r_def dest: permutations_of_setD)

  from \<open>j \<in> R\<close> bipartite_graph i_eligible have min_unmatched: "?min \<in> {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"
    unfolding r_def
    by (intro min_if_finite total_preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] total_preorder_on_imp_total_preorder_on' finite_unmatched_neighbors)
       (auto dest: bipartite_edgeD neighbors_right_subset_left_remove_vertices remove_vertices_subgraph')

  from \<open>j \<in> R\<close> bipartite_graph i_eligible have min_is_min: "\<forall>x \<in> ?ns. (?min, x) \<in> r"
    unfolding r_def
    by (intro ballI min_on_rel_least total_preorder_on'_subset[where S = "L - X" and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X}"] total_preorder_on_imp_total_preorder_on' finite_unmatched_neighbors)
       (auto dest: bipartite_edgeD neighbors_right_subset_left_remove_vertices remove_vertices_subgraph')

  have Y_min: "Y (determ_min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X} r) = Y i"
  proof (rule ccontr)
    assume "Y (determ_min_on_rel {i. i \<notin> Vs M' \<and> {i, j} \<in> G \<setminus> X} r) \<noteq> Y i"
    then consider "Y (determ_min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X} r) < Y i" | "Y i < Y (determ_min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G \<setminus> X} r)"
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
    with \<open>A \<in> sets borel\<close> show ?case
      by measurable
         (use 3 \<open>j \<in> R\<close> in \<open>auto dest: neighbors_right_subset_left_remove_vertices\<close>)
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
  assumes "i < n"
  assumes "i < card L \<Longrightarrow> from_nat_into L i \<notin> X"
  shows "(\<lambda>Y. dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) $ i) \<in> borel_measurable (\<Pi>\<^sub>M i \<in> L - X. U)"
  unfolding dual_sol_def
proof (subst index_vec[OF \<open>i < n\<close>], subst measurable_If_restrict_space_iff, goal_cases)
  case 2
  then show ?case
  proof (rule conjI, subst measurable_If_restrict_space_iff; (intro conjI | simp), goal_cases)
    case 1
    show ?case
    proof (auto, rule measurable_restrict_mono[where A=UNIV], goal_cases)
      case 1
      show ?case
        by measurable (use \<open>i < card L\<close> assms in \<open>auto intro: from_nat_into simp: Vs_enum_inv_from_nat_into_L\<close>)
    qed simp
  next
    case 2
    show ?case
      apply (auto)
      apply (intro borel_measurable_divide borel_measurable_diff borel_measurable_const, rule measurable_compose[ OF dual_component_online_borel_measurable])
      using \<open>i < n\<close> by (auto elim: Vs_enum_inv_rightE)      
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

lemma dual_sol_from_to:
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

lemma measurable_y\<^sub>c[measurable]: "j \<in> R \<Longrightarrow> (\<lambda>Y. y\<^sub>c Y \<pi> i j) \<in> borel_measurable (Pi\<^sub>M (L - {i}) (\<lambda>i. U))"
proof (unfold y\<^sub>c_def, subst measurable_If_restrict_space_iff, subst ranking_Restr_to_vertices[symmetric], goal_cases)
  case 3
  then show ?case
    by (subst linorder_from_keys_Restr) measurable
next
  case 4
  have "set \<pi> \<subseteq> R"
    by simp

  then have *: "(\<lambda>Y. Y (THE i'. {i', j} \<in> ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)) =
    (\<lambda>Y. Y (THE i'. {i',j} \<in> ranking (linorder_from_keys (L - {i}) Y) (G \<setminus> {i}) \<pi>))"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: total_preorder_on_imp_total_preorder_on' simp: linorder_from_keys_Restr)

  from \<open>set \<pi> \<subseteq> R\<close> have **: "restrict_space (Pi\<^sub>M (L - {i}) (\<lambda>i. U)) {Y. j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)} =
    restrict_space (Pi\<^sub>M (L - {i}) (\<lambda>i. U)) {Y. j \<in> Vs (ranking (linorder_from_keys (L - {i}) Y) (G \<setminus> {i}) \<pi>)}"
    by (subst ranking_Restr_to_vertices[symmetric])
       (auto intro: total_preorder_on_imp_total_preorder_on' simp: linorder_from_keys_Restr)

  show ?case
    by (intro conjI, (subst * **)+, rule dual_component_online_borel_measurable)
       (simp_all add: \<open>j \<in> R\<close>)
qed (auto intro: total_preorder_on_imp_total_preorder_on')

lemma dual_sol_from_to_if_funcset:
  shows "Y \<in> (L - X) \<rightarrow> {0..1} \<Longrightarrow> ($) (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
  by (intro dual_sol_from_to) auto

lemma AE_PiM_subset_L_U_from_to:
  assumes "L' \<subseteq> L"
  shows "AE Y in \<Pi>\<^sub>M i \<in> L'. U. Y \<in> L' \<rightarrow> {0..1}"
  using finite_L assms
  by (intro AE_PiM_uniform_measure_PiE_countable)
     (auto intro: countable_finite finite_subset)

lemma AE_U_in_range: "AE y in U. y \<in> {0..1}"
  by (auto intro: AE_uniform_measureI)

lemma funcset_update:
  assumes "Y \<in> L - {i} \<rightarrow> S"
  assumes "y \<in> S"
  shows "Y(i := y) \<in> L \<rightarrow> S"
  using assms
  by auto

lemma (in pair_sigma_finite) AE_pair_measure_swap:
  "AE (x,y) in M1 \<Otimes>\<^sub>M M2. P x y \<Longrightarrow> (AE (y,x) in M2 \<Otimes>\<^sub>M M1. P x y)"
  by (auto simp: case_prod_beta 
           intro!: AE_distrD[where M = "M2 \<Otimes>\<^sub>M M1" and  M' = "M1 \<Otimes>\<^sub>M M2" and P = "\<lambda>(x,y). P x y" and f = "\<lambda>(x,y). (y,x)", simplified case_prod_beta fst_conv snd_conv])
     (subst distr_pair_swap[symmetric])

lemma AE_add_dim_in_range:
  "AE (y,Y) in (U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U)). y \<in> {0..1}"
  apply (subst pair_sigma_finite.AE_pair_measure_swap)
    apply (auto simp: case_prod_beta intro!: pair_sigma_finite.AE_pair_measure AE_uniform_measureI)
     apply measurable
   apply (metis (no_types, lifting) sets.top sets_PiM_cong sets_lborel sets_pair_measure_cong sets_uniform_measure)
  apply measurable
  apply (metis (no_types, lifting) sets.top sets_PiM_cong sets_lborel sets_pair_measure_cong sets_uniform_measure)
  done

lemma AE_add_dim_funcset:
  "AE (y,Y) in (U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U)). Y \<in> L - {i} \<rightarrow> {0..1}"
  using finite_L
  apply (auto intro!: pair_sigma_finite.AE_pair_measure AE_PiM_subset_L_U_from_to simp: case_prod_beta)
   apply measurable
   apply (metis (no_types, lifting) sets.top sets_PiM_cong sets_lborel sets_pair_measure_cong sets_uniform_measure)
  done

lemma AE_split_dim_from_to:
  shows "AE (y, Y) in U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U). Y(i := y) \<in> L \<rightarrow> {0..1}"
  using AE_add_dim_in_range AE_add_dim_funcset
  by (auto simp: case_prod_beta intro!: eventually_mono[OF _ funcset_update, where P = "\<lambda>(y,Y). y \<in> {0..1} \<and> Y \<in> L - {i} \<rightarrow> {0..1}"])

lemma AE_dual_sol_from_to:
  shows "AE Y in \<Pi>\<^sub>M i \<in> L - X. U. ($) (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}" 
  by (rule eventually_mono[OF AE_PiM_subset_L_U_from_to dual_sol_from_to_if_funcset]) blast+

lemma AE_dual_sol_split_dim_from_to:
  shows "AE (y, Y) in U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U). ($) (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
  using eventually_mono[OF AE_split_dim_from_to dual_sol_from_to_if_funcset[where X = "{}"]]
  by (auto simp: case_prod_beta)
  
lemma integrable_dual_component_remove_vertices:
  assumes "i < n"
  assumes "i < card L \<Longrightarrow> from_nat_into L i \<notin> X"
  shows "integrable (\<Pi>\<^sub>M i \<in> L - X. U) (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) $ i)"
  using assms
proof (intro integrableI_nonneg measurable_dual_component, goal_cases)
  case 2
  show ?case
    by (rule eventually_mono[OF AE_dual_sol_from_to], use 2 in auto)
next
  case 3
  have "\<integral>\<^sup>+ Y. ennreal (dual_sol Y (ranking (linorder_from_keys (L - X) Y) (G \<setminus> X) \<pi>) $ i) \<partial>\<Pi>\<^sub>M i \<in> L - X. U \<le> 1/F"
    by (intro subprob_space.nn_integral_le_const prob_space_imp_subprob_space prob_space_PiM_U eventually_mono[OF AE_dual_sol_from_to])
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
    by (rule eventually_mono[OF AE_dual_sol_split_dim_from_to], use 3 in auto)
next
  case 4
  interpret split_dim_prob_space: prob_space "(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
    by (intro prob_space_pair prob_space_PiM) blast+

  have "\<integral>\<^sup>+ (y,Y). ennreal (dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ j) \<partial>(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U)) \<le> 1/F"
    by (intro split_dim_prob_space.nn_integral_le_const eventually_mono[OF AE_dual_sol_split_dim_from_to])
       (use 4 in auto)

  then show ?case
    by (subst case_prod_beta, subst split_comp_eq)
       (simp add: order_le_less_trans)
qed

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

  have the_i': "\<lbrakk>j' \<in> R; j' \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)\<rbrakk>
   \<Longrightarrow> (THE i'. {i',j'} \<in> ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>) \<in> L - {i}" for Y j'
  proof -
    let ?M = "ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>"
    assume "j' \<in> Vs ?M" \<open>j' \<in> R\<close>

    then have the_i': "{(THE i'. {i',j'} \<in> ?M), j'} \<in> ?M"
      "(THE i'. {i',j'} \<in> ?M) \<in> L"
      by (auto intro!: the_ranking_match_left dest: remove_vertices_subgraph')

    have subg: "?M \<subseteq> G \<setminus> {i}"
      by (intro ranking_subgraph) (auto dest: remove_vertices_subgraph')

    with the_i' show "(THE i'. {i',j'} \<in> ?M) \<in> L - {i}"
      apply (auto)
      by (meson edges_are_Vs(1) remove_vertices_not_vs singletonI subsetD)
  qed

  have y\<^sub>c_bounded: "Y \<in> L-{i} \<rightarrow> {0..1} \<Longrightarrow> y\<^sub>c Y \<pi> i j \<in> {0..1}" for Y
  proof (cases "j \<in> Vs (ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>)")
    case True
    let ?M = "ranking (linorder_from_keys L Y) (G \<setminus> {i}) \<pi>"
    assume Y_funcset: "Y \<in> L-{i} \<rightarrow> {0..1}"

    with True \<open>j \<in> R\<close> show ?thesis
      by (auto simp: y\<^sub>c_def dest: the_i')
  qed (simp add: y\<^sub>c_def)

  from \<open>i \<in> L\<close> have integrable_U_dual_sol: "\<lbrakk>k < n; Y \<in> space (Pi\<^sub>M (L - {i}) (\<lambda>i. U))\<rbrakk> \<Longrightarrow> integrable U (\<lambda>x. dual_sol (Y(i := x)) (ranking (linorder_from_keys L (Y(i := x))) G \<pi>) $ k)" for Y k
  proof (intro integrableI_real_bounded measurable_dual_component_fun_upd, goal_cases)
    case 4
    then show ?case sorry
  next
    case 5
    then show ?case sorry
  qed auto

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
    proof (rule integrableI_real_bounded, goal_cases)
      case 1
      from \<open>i \<in> L\<close> \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> show ?case
        using measurable_dual_component_split_dim
        by measurable
    next
      case 2
      then show ?case
        by (rule eventually_mono[OF AE_dual_sol_split_dim_from_to])
           (use \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> in \<open>auto intro!: add_nonneg_nonneg\<close>)
    next
      case 3

      interpret split_dim_prob_space: prob_space "(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
        by (intro prob_space_pair prob_space_PiM) blast+

      have "(\<integral>\<^sup>+ (y,Y). (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ Vs_enum i) +
        (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ (Vs_enum j)) \<partial>U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U)) \<le>
          (\<integral>\<^sup>+ _. 1/F + 1/F \<partial>U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
      proof (rule nn_integral_mono_AE, rule eventually_mono[OF AE_dual_sol_split_dim_from_to], simp add: case_prod_beta)
        fix yY :: "real \<times> ('a \<Rightarrow> real)"
        let ?y = "fst yY" and ?Y = "snd yY"

        assume Pi: "($) (dual_sol (?Y(i := ?y)) (ranking (linorder_from_keys L (?Y(i := ?y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1 / F}"

        with \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> 
        have "dual_sol (?Y(i := ?y)) (ranking (linorder_from_keys L (?Y(i := ?y))) G \<pi>) $ Vs_enum i \<le> 1/F"
          "dual_sol (?Y(i := ?y)) (ranking (linorder_from_keys L (?Y(i := ?y))) G \<pi>) $ Vs_enum j \<le> 1/F"
          by auto

        then show "dual_sol (?Y(i := ?y)) (ranking (linorder_from_keys L (?Y(i := ?y))) G \<pi>) $ Vs_enum i +
         dual_sol (?Y(i := ?y)) (ranking (linorder_from_keys L (?Y(i := ?y))) G \<pi>) $ Vs_enum j
         \<le> 2 / F"
          by linarith
      qed

      also have "\<dots> = 2/F"
        by (simp add: split_dim_prob_space.emeasure_space_1)

      finally show ?case
        by (simp add: order_le_less_trans)
    qed
  next
    case 3
    then show ?case
      by (rule arg_cong2[where f = "integral\<^sup>L"]) auto
  qed auto

  also have "\<dots> \<ge> \<integral>Y. \<integral>y. g y / F * indicator {0..<y\<^sub>c Y \<pi> i j} y \<partial>U + (1 - g (y\<^sub>c Y \<pi> i j)) / F \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U)" (is "_ \<ge> ?integral_bound1")
  proof (intro integral_mono_AE, goal_cases)
    case 1

    show ?case
    proof (intro Bochner_Integration.integrable_add integrableI_real_bounded U_prob_space.borel_measurable_lebesgue_integral, goal_cases)
      case 1
      then show ?case
      proof (subst split_comp_eq[symmetric],
             intro borel_measurable_times borel_measurable_divide measurable_compose[where f = snd and g = g and N = U] measurable_snd, goal_cases)
        case 3
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
        by (intro eventually_mono[OF AE_PiM_subset_L_U_from_to[OF Diff_subset]] integral_nonneg_AE eventually_mono[OF AE_U_in_range])
           (auto intro: mult_nonneg_nonneg g_nonnegI)
    next
      case 3
      have "\<integral>\<^sup>+ Y. ennreal (\<integral>y. g y / F * indicator {0..<y\<^sub>c Y \<pi> i j} y \<partial>U) \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U) \<le> 1/F"
        apply (intro subprob_space.nn_integral_le_const prob_space_imp_subprob_space prob_space_PiM_U)
         apply simp
        apply (rule eventually_mono[OF AE_PiM_subset_L_U_from_to])
         apply blast
        apply auto
        apply (rule integral_real_bounded)
        apply simp
        apply (intro subprob_space.nn_integral_le_const prob_space_imp_subprob_space)
          apply blast
         apply simp
        apply (rule eventually_mono[OF AE_U_in_range])
         apply simp
        apply (auto intro: mult_le_one g_less_eq_OneI)
        done

      then show ?case
        by (simp add: order_le_less_trans)
    next
      case 4
      from \<open>j \<in> R\<close> show ?case
        by measurable
    next
      case 5
      then show ?case 
        by (rule eventually_mono[OF AE_PiM_subset_L_U_from_to])
           (auto intro!: g_less_eq_OneI dest: y\<^sub>c_bounded)
    next
      case 6

      have "\<integral>\<^sup>+ x. (1 - g (y\<^sub>c x \<pi> i j)) / F \<partial>Pi\<^sub>M (L - {i}) (\<lambda>i. U) \<le> 1/F"
        apply (intro subprob_space.nn_integral_le_const prob_space_imp_subprob_space prob_space_PiM_U)
         apply simp
        apply (rule eventually_mono[OF AE_PiM_subset_L_U_from_to])
         apply (auto intro!: g_nonnegI dest: y\<^sub>c_bounded)
        done

      then show ?case
        by (simp add: order_le_less_trans)
    qed
  next
    case 2
    show ?case
    proof (intro integrableI_real_bounded U_prob_space.borel_measurable_lebesgue_integral, goal_cases)
      case 1
      from \<open>i \<in> L\<close> \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close>  show ?case
        using measurable_dual_component_split_dim
        by measurable
    next
      case 2
      from \<open>Vs_enum i < n\<close> \<open>Vs_enum j < n\<close> show ?case
        by (intro eventually_mono[OF AE_PiM_subset_L_U_from_to[OF Diff_subset]] integral_nonneg_AE eventually_mono[OF AE_U_in_range])
           (auto dest!: funcset_update dual_sol_from_to_if_funcset[where X = "{}", simplified] intro!: add_nonneg_nonneg)
    next
      case 3
      interpret L'_prob_space: prob_space "\<Pi>\<^sub>M i \<in> L - {i}. U"
        by (intro prob_space_PiM) blast

      have "\<integral>\<^sup>+Y. (U_prob_space.expectation (\<lambda>y. dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i +
                                              dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j)) 
            \<partial>Pi\<^sub>M (L - {i}) (\<lambda>i. U) \<le> \<integral>\<^sup>+_. 2/F \<partial>Pi\<^sub>M (L - {i}) (\<lambda>i. U)"
      proof (intro nn_integral_mono_AE eventually_mono[OF AE_PiM_subset_L_U_from_to[OF Diff_subset]], simp, 
             intro integral_real_bounded U_prob_space.nn_integral_le_const eventually_mono[OF AE_U_in_range], goal_cases)
        case (3 Y y)
        then have "($) (dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>)) \<in> {..<n} \<rightarrow> {0..1/F}"
          by (auto dest!: funcset_update dual_sol_from_to_if_funcset[where X = "{}", simplified])

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
    from finite_L have AE_linorder: "AE Y in PiM (L - {i}) (\<lambda>i. U). Y \<in> space (PiM (L - {i}) (\<lambda>i. U)) \<and> Y \<in> L-{i} \<rightarrow> {0..1} \<and> linorder_on (L - {i}) (linorder_from_keys (L - {i}) Y)"
      apply (subst eventually_conj_iff, intro conjI AE_PiM_subset_L_U_from_to[OF Diff_subset])
      apply (auto intro!: AE_PiM_subset_L_U_from_to AE_distrD[OF _ almost_everywhere_linorder[where B = "L - {i}"]])
      apply measurable
      sorry

    
    show ?case
    proof (rule eventually_mono[OF AE_linorder])
      fix Y :: "'a \<Rightarrow> real"
      assume Y: "Y \<in> space (PiM (L - {i}) (\<lambda>i. U)) \<and> Y \<in> L-{i} \<rightarrow> {0..1} \<and> linorder_on (L - {i}) (linorder_from_keys (L - {i}) Y)"

      have integrable_offline_bound: "integrable U (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y)"
      proof (intro integrableI_real_bounded, goal_cases)
        case 1
        then show ?case
          by measurable
      next
        case 2
        then show ?case
          by (rule eventually_mono[OF AE_U_in_range])
            (auto intro: mult_nonneg_nonneg g_nonnegI)
      next
        case 3
        have "\<integral>\<^sup>+ y. ennreal (g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y) \<partial>U \<le> 1/F"
          by (intro subprob_space.nn_integral_le_const prob_space_imp_subprob_space eventually_mono[OF AE_U_in_range])
            (auto intro: mult_le_one g_less_eq_OneI)

        then show ?case
          by (simp add: order_le_less_trans)
      qed

      have *: "(1 - g (y\<^sub>c Y \<pi> i j)) / F = U_prob_space.expectation (\<lambda>y. (1 - g (y\<^sub>c Y \<pi> i j)) / F)" for Y
        by (simp add: measure_def U_prob_space.emeasure_space_1)

      have "U_prob_space.expectation (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y) + (1 - g (y\<^sub>c Y \<pi> i j)) / F = 
      U_prob_space.expectation (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y + (1 - g (y\<^sub>c Y \<pi> i j)) / F)"
        by (subst *, intro Bochner_Integration.integral_add[symmetric] integrable_offline_bound, auto)

      also have "\<dots> \<le> U_prob_space.expectation (\<lambda>y. dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i +
                         dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j)"
      proof (intro integral_mono_AE Bochner_Integration.integrable_add integrable_offline_bound, goal_cases)
        case 2
        with \<open>Vs_enum i < n\<close> Y show ?case
          by (auto intro: integrable_U_dual_sol)
      next
        case 3
        with \<open>Vs_enum j < n\<close> Y show ?case
          by (auto intro: integrable_U_dual_sol)
      next
        case 4
        then show ?case
          apply (rule eventually_mono[where P = "\<lambda>y. y \<in> {0..1}"])
          subgoal 
            by (auto intro: AE_uniform_measureI)
          subgoal for y
          proof (rule add_mono, goal_cases)
            case 1
            then show ?case
              apply (auto simp: indicator_times_eq_if)
              subgoal
                unfolding dual_sol_def
                using \<open>i \<in> L\<close> \<open>j \<in> R\<close> \<open>{i,j} \<in> G\<close>
                apply (subst index_vec[OF  \<open>Vs_enum i < n\<close>])
                apply (subst (asm) y\<^sub>c_fun_upd_eq[where y = y, symmetric])
                apply blast
                apply (drule dominance[OF \<open>i \<in> L\<close> \<open>j \<in> R\<close> \<open>{i,j} \<in> G\<close>, where Y = "Y(i:=y)", simplified])
                apply (auto)
                 apply (metis L_enum_less_card Vs_enum_L)+
                done
              subgoal
                unfolding dual_sol_def
                using \<open>Vs_enum i < n\<close> \<open>i \<in> L\<close>
                apply (auto intro: g_nonnegI g_less_eq_OneI)
                apply (metis L_enum_less_card Vs_enum_L)
                done
              done
          next
            case 2
            with \<open>j \<in> R\<close> show ?case
              apply (subst y\<^sub>c_fun_upd_eq[where y = y, symmetric])
              apply blast
              apply (rule monotonicity)
              using 2 Y \<open>i \<in> L\<close> \<open>j \<in> R\<close> \<open>{i,j} \<in> G\<close> apply (auto dest: funcset_update)
              done
          qed
          done
      qed simp

      finally show "U_prob_space.expectation (\<lambda>y. g y / F * indicat_real {0..<y\<^sub>c Y \<pi> i j} y) + (1 - g (y\<^sub>c Y \<pi> i j)) / F
         \<le> U_prob_space.expectation (\<lambda>y. dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum i 
                                  + dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ Vs_enum j)"
        .
    qed
  qed

  finally have "?Ei_plus_Ej \<ge> ?integral_bound1" .

  have "?integral_bound1 = \<integral>Y. \<integral>y. g y * indicator {0..<y\<^sub>c Y \<pi> i j} y \<partial>U + (1 - g (y\<^sub>c Y \<pi> i j)) \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U) / F "
    by (auto simp flip: add_divide_distrib)

  also have "\<dots> \<ge> \<integral>Y. F \<partial>(\<Pi>\<^sub>M i \<in> L - {i}. U) / F" (is "_ \<ge> ?integral_bound2")
  proof (subst div_F_less_eq_cancel, intro integral_mono_AE, goal_cases)
    case 1
    show ?case
      by (rule integrableI_real_bounded)
         (use F_gt_0 in \<open>auto simp: emeasure_space_PiM_U\<close>)
  next
    case 2
      \<comment> \<open>proven above\<close>
    then show ?case sorry
  next
    case 3
    then show ?case
      by (rule eventually_mono[OF AE_PiM_subset_L_U_from_to])
         (auto intro!: g_integral_bound dest: y\<^sub>c_bounded)
  qed

  finally have "?integral_bound1 \<ge> ?integral_bound2" .

  from F_gt_0 have "?integral_bound2 = 1"
    by (auto simp: measure_def emeasure_space_PiM_U)

  with \<open>?Ei_plus_Ej \<ge> ?integral_bound1\<close> \<open>?integral_bound1 \<ge> ?integral_bound2\<close> show ?thesis
    by linarith
qed

end
