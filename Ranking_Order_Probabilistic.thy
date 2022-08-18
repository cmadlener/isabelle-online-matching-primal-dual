theory Ranking_Order_Probabilistic
  imports
    Ranking_Order
    "Jordan_Normal_Form.Matrix"
    "Treaps.Random_List_Permutation"
begin

hide_const Finite_Cartesian_Product.vec Finite_Cartesian_Product.vec.vec_nth

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

lemma restrict_space_UNIV[simp]: "restrict_space M UNIV = M"
  unfolding restrict_space_def
  by (auto simp: measure_of_of_measure)

lemma borel_measurable_restrict_space_empty[simp,intro]:
  fixes f :: "'a \<Rightarrow> 'b :: {banach,second_countable_topology}"
  shows "f \<in> borel_measurable (restrict_space M {})"
  by (auto intro: borel_measurable_integrable simp: integrable_restrict_space)

lemma linorder_from_keys_preorder_on[intro]: "preorder_on A (linorder_from_keys A f)"
  unfolding linorder_from_keys_def preorder_on_def
  by (auto simp: refl_on_def trans_def)

lemma linorder_from_keys_preorder[intro]: "linorder_from_keys A f \<in> preorders_on A"
  by (auto intro: preorders_onI)

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
  fixes \<pi> :: "'a list" and Y_measure U
  fixes g :: "real \<Rightarrow> real" and F :: real

  defines "U \<equiv> uniform_measure lborel {0..1::real}"
  defines "Y_measure \<equiv> \<Pi>\<^sub>M i \<in> L. U"

  assumes perm: "\<pi> \<in> permutations_of_set R"

  assumes g_from_to: "g \<in> {0..1} \<rightarrow> {0..1}"
  assumes g_mono: "mono_on g {0..1}"
  assumes g_One: "g 1 = 1"
  assumes g_borel[measurable]: "g \<in> borel_measurable borel"

  assumes F_gt_0: "0 < F"
begin


sublocale U_prob_space: prob_space U
  unfolding U_def
  by (auto intro: prob_space_uniform_measure)

lemmas U_prob_space.prob_space_axioms[intro]

sublocale prob_space Y_measure
  unfolding Y_measure_def
  by (auto intro: prob_space_PiM)

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

lemma n_sum: "n = card L + card R"
  using bipartite_graph parts_minimal finite_L finite_R
  by (auto dest: bipartite_disjointD simp: card_Un_disjoint n_def)

lemma geq_L_less_n_less_R: "card L \<le> i \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto simp: n_sum)

lemma geq_L_less_n_less_R': "\<not> i < card L \<Longrightarrow> i < n \<Longrightarrow> i - card L < card R"
  by (auto intro: geq_L_less_n_less_R)

lemma Vs_cases: 
  assumes "x \<in> Vs G"
  obtains "x \<in> L \<and> x \<notin> R" | "x \<in> R \<and> x \<notin> L"
  using assms parts_minimal bipartite_graph
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
  using bipartite_graph
  unfolding Vs_enum_def Vs_enum_inv_def
  by (auto dest: bipartite_disjointD)

lemma Vs_enum_less_n: "x \<in> Vs G \<Longrightarrow> Vs_enum x < n"
  by (auto elim!: Vs_cases simp: Vs_enum_L Vs_enum_R intro: L_enum_less_n R_enum_less_n)

lemma
  shows Vs_inv_enum[simp]: "x \<in> Vs G \<Longrightarrow> Vs_enum_inv (Vs_enum x) = x"
    and Vs_enum_inv[simp]: "i < n \<Longrightarrow> Vs_enum (Vs_enum_inv i) = i"
  using finite_L finite_R
   apply (auto elim!: Vs_cases simp: Vs_enum_inv_def Vs_enum_def n_sum dest: L_enum_less_card intro!: from_nat_into)
  by (metis Un_iff Vs_cases add.right_neutral card.empty from_nat_into parts_minimal)

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
  by (metis Vs_enum_inv_def add.right_neutral card.empty from_nat_into n_sum)

lemma preorder_on_neighbors_linorder_from_keys[intro]:
  assumes "j \<in> R"
  shows "preorder_on' {i. {i,j} \<in> G} (linorder_from_keys L Y)"
  using assms perm
  by (auto intro: preorder_on_neighborsI[where js = \<pi>] dest: permutations_of_setD)

lemma ranking_measurable:
  assumes "set js \<subseteq> R"
  shows "(\<lambda>Y. ranking (linorder_from_keys L Y) G js) \<in> Y_measure \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys L" _ "count_space (preorders_on L)"], goal_cases)
  case 1
  from finite_L show ?case
    unfolding Y_measure_def U_def
    by measurable
next
  case 2
  from finite_subsets \<open>set js \<subseteq> R\<close> show ?case
    by (subst measurable_count_space_eq2)
       (auto dest: ranking_subgraph)
qed

lemma in_vertices_borel_measurable_count_space:
  "(\<lambda>M. i \<in> Vs M) \<in> borel_measurable (count_space {M. M \<subseteq> G})"
  by measurable

lemma in_vertices_Measurable_pred_count_space:
  "Measurable.pred (count_space {M. M \<subseteq> G}) (\<lambda>M. i \<in> Vs M)"
  by measurable

lemmas in_vertices_borel_measurable[measurable] = measurable_compose[OF ranking_measurable in_vertices_borel_measurable_count_space]
lemmas in_vertices_Measurable_pred[measurable] = measurable_compose[OF ranking_measurable in_vertices_Measurable_pred_count_space]

lemma 
  assumes "A \<in> sets borel"
  assumes "finite I" "i \<in> I"
  shows "Measurable.pred (Pi\<^sub>M I (\<lambda>_. lborel)) (\<lambda>Y. Y i \<in> A)"
  using assms
  by measurable


lemma online_matched_with_borel_iff:
  fixes Y :: "'a \<Rightarrow> real"
  defines "r \<equiv> linorder_from_keys L Y"
  assumes "j \<in> R" "A \<in> sets borel"

  \<comment> \<open>should we lift this assumption (since it is always true)? would need to use \<^term>\<open>takeWhile (\<lambda>x. x \<noteq> j)\<close>
      and \<^term>\<open>dropWhile\<close> in statement\<close>
  assumes \<pi>_decomp: "\<pi> = \<pi>' @ j # \<pi>''" "j \<notin> set \<pi>'" "j \<notin> set \<pi>''"
  defines "M' \<equiv> ranking r G \<pi>'"

  shows "j \<in> Vs (ranking r G \<pi>) \<and> Y (THE i. {i,j} \<in> ranking r G \<pi>) \<in> A
    \<longleftrightarrow> (\<exists>i\<in>{i. {i,j} \<in> G}. i \<notin> Vs M' \<and> Y i \<in> A \<and>
          (\<forall>i'\<in>{i. {i,j} \<in> G}. i' \<notin> Vs M' \<longrightarrow> Y i \<le> Y i'))"
  (is "j \<in> Vs ?M \<and> Y (THE i. {i,j} \<in> ?M) \<in> A \<longleftrightarrow> ?F")
proof
  assume j_matched: "j \<in> Vs ?M \<and> Y (THE i. {i,j} \<in> ?M) \<in> A"
  let ?i = "min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G} r"

  from \<pi>_decomp have "?M = ranking' r G M' (j#\<pi>'')"
    unfolding M'_def
    by (simp add: ranking_append)

  from \<pi>_decomp \<open>j \<in> R\<close> bipartite_graph perm have "j \<notin> Vs M'"
    unfolding M'_def r_def
    by (intro unmatched_R_in_ranking_if)
       (auto dest: bipartite_disjointD permutations_of_setD)

  have neighbor_ex: "\<exists>i\<in>{i. {i,j} \<in> G}. i \<notin> Vs M'" (is "?Ex")
  proof (rule ccontr)
    assume "\<not> ?Ex"

    then have step_unchanged: "step r G M' j = M'"
      by (auto simp: step_def)

    with \<pi>_decomp have M: "?M = ranking' r G M' \<pi>''"
      unfolding ranking'_def M'_def
      by simp

    from \<pi>_decomp \<open>j \<in> R\<close> \<open>j \<notin> Vs M'\<close> perm step_unchanged bipartite_graph have "j \<notin> Vs ?M"
      by (subst M, intro unmatched_R_in_ranking_if, unfold r_def)
         (auto dest: permutations_of_setD bipartite_disjointD)
    
    with j_matched show False
      by blast
  qed

  with \<open>j \<notin> Vs M'\<close> have step_eq: "step r G M' j = insert {?i, j} M'"
    by (auto simp add: step_def)

  from neighbor_ex \<open>j \<in> R\<close> bipartite_graph have i_unmatched: "?i \<in> {i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
    by (intro min_if_finite preorder_on'_subset[where S = L and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"] finite_unmatched_neighbors)
       (auto simp: r_def intro: preorder_on_imp_preorder_on'  dest: bipartite_edgeD)

  from neighbor_ex \<open>j \<in> R\<close> bipartite_graph have i_min: 
    "\<not>(\<exists>i'\<in>{i. i \<notin> Vs M' \<and> {i,j} \<in> G}. (i',?i) \<in> r \<and> (?i,i') \<notin> r)"
    by (intro min_if_finite preorder_on'_subset[where S = L and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"] finite_unmatched_neighbors)
       (auto simp: r_def intro: preorder_on_imp_preorder_on'  dest: bipartite_edgeD)


  have the_i: "(THE i. {i,j} \<in> ?M) = ?i"
  proof (intro the_match matching_ranking, goal_cases)
    case 2
    from perm show ?case
      by (auto dest: permutations_of_setD simp: r_def)
  next
    case 4
    from \<pi>_decomp step_eq show ?case
      by (auto simp add: ranking_append ranking_Cons M'_def intro: ranking_mono)
  qed (use finite_vs in simp_all)

  show ?F
  proof (intro bexI[of _ ?i] conjI ballI impI, goal_cases)
    case (3 i')
    show ?case
    proof (rule ccontr, simp add: not_le)
      assume "Y i' < Y ?i"
      with 3 i_unmatched \<open>j \<in> R\<close> have "(i',?i) \<in> r \<and> (?i,i') \<notin> r"
        unfolding r_def linorder_from_keys_def
        by (auto dest: neighbors_right_subset_left)

      with 3 i_min show False
        by blast
    qed
  qed (use i_unmatched j_matched in \<open>simp_all add: the_i\<close>)
next
  assume eligible_neighbor: ?F
  let ?ns = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"

  from eligible_neighbor obtain i where 
    i_eligible: "i \<notin> Vs M'" "{i,j} \<in> G" and
    Y_i: "Y i \<in> A" and
    i_min_on_r: "\<forall>i'\<in>?ns. Y i \<le> Y i'"
    by auto

  from \<pi>_decomp have "?M = ranking' r G M' (j#\<pi>'')"
    unfolding ranking'_def M'_def
    by simp

  from \<pi>_decomp \<open>j \<in> R\<close> bipartite_graph perm have j_unmatched_before: "j \<notin> Vs M'"
    unfolding M'_def r_def
    by (intro unmatched_R_in_ranking_if)
       (auto dest: bipartite_disjointD permutations_of_setD)

  let ?min = "min_on_rel ?ns r"

  from j_unmatched_before i_eligible have step_eq: "step r G M' j = insert {?min, j} M'"
    unfolding step_def
    by auto

  with finite_vs perm \<pi>_decomp \<open>j \<in> R\<close> have the_i_step: "(THE i. {i,j} \<in> step r G M' j) = ?min"
    unfolding M'_def
    by (intro the_match matching_step matching_ranking)
       (auto intro!: preorder_on_neighbors_linorder_from_keys simp: r_def dest: permutations_of_setD)

  from \<open>j \<in> R\<close> bipartite_graph i_eligible have min_unmatched: "?min \<in> {i. i \<notin> Vs M' \<and> {i,j} \<in> G}"
    unfolding r_def
    by (intro min_if_finite preorder_on'_subset[where S = L and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"] preorder_on_imp_preorder_on' finite_unmatched_neighbors)
       (auto dest: bipartite_edgeD)

  from \<open>j \<in> R\<close> bipartite_graph i_eligible have min_is_min: "\<not>(\<exists>x \<in> ?ns. (x, ?min) \<in> r \<and> (?min, x) \<notin> r)"
    unfolding r_def
    by (intro min_if_finite preorder_on'_subset[where S = L and T = "{i. i \<notin> Vs M' \<and> {i,j} \<in> G}"] preorder_on_imp_preorder_on' finite_unmatched_neighbors)
       (auto dest: bipartite_edgeD)

  have Y_min: "Y (min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G} r) = Y i"
  proof (rule ccontr)
    assume "Y (min_on_rel {i. i \<notin> Vs M' \<and> {i, j} \<in> G} r) \<noteq> Y i"
    then consider "Y (min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G} r) < Y i" | "Y i < Y (min_on_rel {i. i \<notin> Vs M' \<and> {i,j} \<in> G} r)"
      by linarith

    then show False
    proof cases
      case 1     
      with min_unmatched i_min_on_r show ?thesis
        by auto
    next
      case 2
      with \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> bipartite_graph min_unmatched have "(i, ?min) \<in> r" "(?min, i) \<notin> r"
        unfolding r_def linorder_from_keys_def
        by (auto dest: bipartite_edgeD)

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
    from finite_vs perm \<pi>_decomp step_eq \<open>j \<in> R\<close> have "(THE i. {i,j} \<in> ranking r G \<pi>) = ?min"
    unfolding M'_def
    by (intro the_match matching_step matching_ranking)
       (auto intro!: preorder_on_neighbors_linorder_from_keys intro: ranking_mono dest: permutations_of_setD simp: r_def ranking_append ranking_Cons)

  with Y_min Y_i show ?case
    by simp
  qed
qed

lemma dual_component_online_in_sets:
  assumes "j \<in> R"
  assumes "A \<in> sets (borel::real measure)"
  shows  "{Y \<in> space (Pi\<^sub>M L (\<lambda>i. uniform_measure lborel {0..1})). j \<in> Vs (ranking (linorder_from_keys L Y) G \<pi>) \<and> 
    Y (THE l. {l, j} \<in> ranking (linorder_from_keys L Y) G \<pi>) \<in> A} \<in> sets (Pi\<^sub>M L (\<lambda>i. uniform_measure lborel {0..1}))"
proof -
  from \<open>j \<in> R\<close> perm obtain pre suff where \<pi>_decomp: "\<pi> = pre @ j # suff" "j \<notin> set pre" "j \<notin> set suff"
    by (metis permutations_of_setD split_list_distinct)

  with perm have set_pre: "set pre \<subseteq> R"
    by (auto dest: permutations_of_setD)

  show ?thesis
  proof (intro predE, subst online_matched_with_borel_iff[OF assms \<pi>_decomp], intro pred_intros_finite pred_intros_logic, goal_cases)
    case (2 i)
    with set_pre show ?case
      by measurable (auto simp: Y_measure_def U_def)
  next
    case (3 i)
    with \<open>A \<in> sets borel\<close> show ?case
      by measurable
         (use 3 \<open>j \<in> R\<close> in \<open>auto dest: neighbors_right_subset_left\<close>)
  next
    case (5 i i')
    with set_pre show ?case
      by measurable (auto simp: Y_measure_def U_def)
  next
    case (6 i i')
    with \<open>j \<in> R\<close> have "i \<in> L" "i' \<in> L"
      by (auto dest: neighbors_right_subset_left)

    then show ?case
      by measurable
  qed (rule finite_neighbors)+
qed

lemma dual_component_online_borel_measurable:
  assumes "i \<in> R"
  shows "(\<lambda>x. x (THE l. {l, i} \<in> ranking (linorder_from_keys L x) G \<pi>)) \<in> borel_measurable (restrict_space Y_measure {x. i \<in> Vs (ranking (linorder_from_keys L x) G \<pi>)})"
proof (rule measurableI, goal_cases)
  case (1 Y)
  then show ?case
    by simp
next
  case (2 A)
  show ?case
  proof (simp add: space_restrict_space sets_restrict_space Y_measure_def U_def image_def vimage_def Int_def,
      rule bexI[of _ "{Y \<in> space Y_measure. i \<in> Vs (ranking (linorder_from_keys L Y) G \<pi>) \<and> Y (THE l. {l,i} \<in> ranking (linorder_from_keys L Y) G \<pi>) \<in> A}"], goal_cases)
    case 2
    from \<open>i \<in> R\<close> \<open>A \<in> sets borel\<close> show ?case
      unfolding Y_measure_def U_def
      by (rule dual_component_online_in_sets)
  qed (unfold Y_measure_def U_def, blast)
qed

lemma measurable_dual_component:
  assumes "i < n"
  shows "(\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i) \<in> borel_measurable Y_measure"
  unfolding dual_sol_def
proof (subst index_vec[OF assms], subst measurable_If_restrict_space_iff, goal_cases)
  case 2
  then show ?case
  proof (rule conjI, subst measurable_If_restrict_space_iff; (intro conjI | simp), goal_cases)
    case 1
    show ?case
    proof (auto, rule measurable_restrict_mono[where A=UNIV], goal_cases)
      case 1
      with g_borel show ?case
        unfolding Y_measure_def U_def
        by (measurable, use \<open>i < card L\<close> in \<open>auto intro: from_nat_into simp: Vs_enum_inv_from_nat_into_L\<close>)
    qed simp
  next
    case 2
    show ?case
      apply auto
      apply measurable
       apply (rule dual_component_online_borel_measurable)
      using \<open>i < n\<close> by (auto elim: Vs_enum_inv_rightE)      
  qed
qed (use perm in \<open>measurable, auto dest: permutations_of_setD\<close>)

lemma measurable_dual_component_split_dim:
  assumes "i \<in> L"
  assumes "j < n"
  shows "(\<lambda>(y,Y). dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ j) \<in> borel_measurable (U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
  using measurable_compose[OF measurable_add_dim' measurable_dual_component[unfolded Y_measure_def]] assms
  by (auto simp: case_prod_beta)

lemma g_nonnegI: "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 0 \<le> g x"
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

lemma dual_sol_from_to:
  assumes Y_nonneg: "\<And>i. i \<in> L \<Longrightarrow> 0 \<le> Y i"
  assumes Y_less_eq_One: "\<And>i. i \<in> L \<Longrightarrow> Y i \<le> 1"
  shows "($) (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}"
  using F_gt_0 perm bipartite_graph
  unfolding dual_sol_def
  apply (auto intro!: g_nonnegI g_less_eq_OneI Y_nonneg Y_less_eq_One elim!: Vs_enum_inv_leftE)
     apply (auto elim!: Vs_enum_inv_rightE intro!: the_ranking_match_left bipartite_empty  dest: permutations_of_setD bipartite_disjointD)
  done

lemma dual_sol_from_to_if_funcset:
  shows "Y \<in> L \<rightarrow> {0..1} \<Longrightarrow> ($) (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}"
  by (intro dual_sol_from_to) auto

lemma AE_Y_measure_from_to:
  shows "AE Y in Y_measure. Y \<in> L \<rightarrow> {0..1}"
  unfolding Y_measure_def U_def
  using finite_L
  by (intro AE_PiM_uniform_measure_PiE_countable)
     (auto intro: countable_finite)

lemma funcset_update:
  assumes "Y \<in> L - {i} \<rightarrow> S"
  assumes "y \<in> S"
  shows "Y(i := y) \<in> L \<rightarrow> S"
  using assms
  by auto

lemma (in pair_sigma_finite) AE_pair_measure_swap:
  "AE (x,y) in M1 \<Otimes>\<^sub>M M2. P x y \<Longrightarrow> (AE (y,x) in M2 \<Otimes>\<^sub>M M1. P x y)"
  apply (auto simp: case_prod_beta intro!: AE_distrD[where M = "M2 \<Otimes>\<^sub>M M1" and  M' = "M1 \<Otimes>\<^sub>M M2" and P = "\<lambda>(x,y). P x y" and f = "\<lambda>(x,y). (y,x)", simplified case_prod_beta fst_conv snd_conv])
  apply (subst distr_pair_swap[symmetric])
  apply blast
  done

lemma AE_add_dim_in_range:
  "AE (y,Y) in (U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U)). y \<in> {0..1}"
  apply (subst pair_sigma_finite.AE_pair_measure_swap)
    apply (auto simp: case_prod_beta intro!: pair_sigma_finite.AE_pair_measure)
  unfolding U_def
     apply measurable
    apply (auto intro!: AE_uniform_measureI)
   apply measurable
   apply (metis (no_types, lifting) sets.top sets_PiM_cong sets_lborel sets_pair_measure_cong sets_uniform_measure)
  done

lemma AE_add_dim_funcset:
  "AE (y,Y) in (U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U)). Y \<in> L - {i} \<rightarrow> {0..1}"
  apply (auto intro!: pair_sigma_finite.AE_pair_measure simp: case_prod_beta)
  unfolding U_def
   apply measurable
  using finite_L apply simp
    apply blast
   apply simp
  apply (rule AE_PiM_uniform_measure_PiE_countable)
  using finite_L apply (auto intro: countable_finite)
  done

lemma AE_split_dim_from_to:
  shows "AE (y, Y) in U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U). Y(i := y) \<in> L \<rightarrow> {0..1}"
  using AE_add_dim_in_range AE_add_dim_funcset
  by (auto simp: case_prod_beta intro!: eventually_mono[OF _ funcset_update, where P = "\<lambda>(y,Y). y \<in> {0..1} \<and> Y \<in> L - {i} \<rightarrow> {0..1}"])

lemma AE_dual_sol_from_to:
  shows "AE Y in Y_measure. ($) (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}" 
  by (rule eventually_mono[OF AE_Y_measure_from_to dual_sol_from_to_if_funcset])

lemma AE_dual_sol_split_dim_from_to:
  shows "AE (y, Y) in U \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) (\<lambda>i. U). ($) (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}"
  using eventually_mono[OF AE_split_dim_from_to dual_sol_from_to_if_funcset]
  by (auto simp: case_prod_beta)
  
lemma integrable_dual_component:
  assumes "i < n"
  shows "integrable Y_measure (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i)"
  using assms
proof (intro integrableI_nonneg measurable_dual_component, goal_cases)
  case 2
  show ?case
    by (rule eventually_mono[OF AE_dual_sol_from_to], use 2 in auto)
next
  case 3
  have "\<integral>\<^sup>+ Y. ennreal (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i) \<partial>Y_measure \<le>
    \<integral>\<^sup>+ _. 1/F \<partial>Y_measure"
    by (rule nn_integral_mono_AE, rule eventually_mono[OF AE_dual_sol_from_to], use 3 in auto)

  also have "\<dots> = 1/F"
    by (simp add: emeasure_space_1)

  finally show ?case
    by (simp add: order_le_less_trans)
qed

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

  have "\<integral>\<^sup>+ (y,Y). ennreal (dual_sol (Y(i := y)) (ranking (linorder_from_keys L (Y(i := y))) G \<pi>) $ j) \<partial>(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U)) \<le>
    \<integral>\<^sup>+_. 1/F \<partial>(U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
    by (rule nn_integral_mono_AE, rule eventually_mono[OF AE_dual_sol_split_dim_from_to], use 4 in auto)

  also have "\<dots> = 1/F"
    by  (simp add: split_dim_prob_space.emeasure_space_1)

  finally show ?case
    by (subst case_prod_beta, subst split_comp_eq)
       (simp add: order_le_less_trans)
qed

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
    unfolding Y_measure_def
    by (simp add: insert_absorb)

  also have "\<dots> = integral\<^sup>L (distr (U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> (L - {i}). U))
    (Pi\<^sub>M (insert i (L - {i})) (\<lambda>_. U))
    (\<lambda>(y,Y). Y(i := y))) ?i_plus_j"
    by (intro arg_cong2[where f = "integral\<^sup>L"] distr_pair_PiM_eq_PiM[symmetric] prob_space_uniform_measure)
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
         (auto simp: insert_absorb intro: measurable_dual_component[simplified Y_measure_def])
  qed

  also have "\<dots> = \<integral>Y. \<integral>y. ?i_plus_j (Y(i := y)) \<partial>U \<partial>(\<Pi>\<^sub>M i \<in> (L - {i}). U)"
  proof (subst pair_sigma_finite.integral_snd, goal_cases)
    case 1
    then show ?case
      by (auto intro: pair_sigma_finite.intro prob_space_imp_sigma_finite prob_space_PiM)
  next
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

      have "(\<integral>\<^sup>+ (y,Y). ennreal ((dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ (Vs_enum i)) +
        (dual_sol (Y(i:=y)) (ranking (linorder_from_keys L (Y(i:=y))) G \<pi>) $ (Vs_enum j))) \<partial>U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U)) \<le>
          (\<integral>\<^sup>+ _. 1/F + 1/F \<partial>U \<Otimes>\<^sub>M (\<Pi>\<^sub>M i \<in> L - {i}. U))"
      proof (rule nn_integral_mono_AE, rule eventually_mono[OF AE_dual_sol_split_dim_from_to], simp add: case_prod_beta)
        fix yY :: "real \<times> ('a \<Rightarrow> real)"
        let ?y = "fst yY" and ?Y = "snd yY"

        assume Pi: "($) (dual_sol (?Y(i := ?y)) (ranking (linorder_from_keys L (?Y(i := ?y))) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1 / F}"

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
        by (subst case_prod_beta, subst split_comp_eq)
           (simp add: order_le_less_trans)
    qed
  next
    case 3
    then show ?case
      by (rule arg_cong2[where f = "integral\<^sup>L"]) auto
  qed

  show ?thesis
    sorry
qed

end

end