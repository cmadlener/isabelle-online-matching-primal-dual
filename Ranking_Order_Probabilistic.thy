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
  fixes \<pi> :: "'a list" and Y_measure
  fixes g :: "real \<Rightarrow> real" and F :: real

  defines "Y_measure \<equiv> \<Pi>\<^sub>M i \<in> L. uniform_measure lborel {0..1::real}"

  assumes perm: "\<pi> \<in> permutations_of_set R"

  assumes g_from_to: "g \<in> {0..1} \<rightarrow> {0..1}"
  assumes g_mono: "mono_on g {0..1}"
  assumes g_One: "g 1 = 1"
  assumes g_borel[measurable]: "g \<in> borel_measurable borel"

  assumes F_gt_0: "0 < F"
begin

sublocale prob_space Y_measure
  unfolding Y_measure_def
  by (auto intro!: prob_space_PiM prob_space_uniform_measure)

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

lemma Vs_enum_inv_rightE:
  assumes "i < n"
  assumes "\<not> i < card L"
  obtains j where "j \<in> R" "Vs_enum_inv i = j"
  using assms
  by (metis Vs_enum_inv_def add.right_neutral card.empty from_nat_into n_sum)

lemma ranking_subgraph:
  assumes "r \<in> preorders_on L"
  shows "ranking r G \<pi> \<subseteq> G"
  using assms perm graph
  by (intro ranking'_subgraph)
     (auto intro: preorder_on_neighborsI ranking'_subgraph dest: permutations_of_setD)

lemma ranking_measurable:
  "(\<lambda>Y. ranking (linorder_from_keys L Y) G \<pi>) \<in> Y_measure \<rightarrow>\<^sub>M count_space {M. M \<subseteq> G}"
proof (rule measurable_compose[of "linorder_from_keys L" _ "count_space (preorders_on L)" "\<lambda>r. ranking r G \<pi>"], goal_cases)
  case 1
  from finite_L show ?case
    unfolding Y_measure_def
    by measurable
next
  case 2
  from finite_subsets show ?case
    by (subst measurable_count_space_eq2)
       (auto dest: ranking_subgraph)
qed

lemma in_vertices_measurable_count_space:
  "(\<lambda>M. i \<in> Vs M) \<in> count_space {M. M \<subseteq> G} \<rightarrow>\<^sub>M count_space UNIV"
  by measurable

lemmas in_vertices_measurable[measurable] = measurable_comp[OF ranking_measurable in_vertices_measurable_count_space, simplified comp_def]

lemma measurable_dual_component:
  assumes "i < n"
  shows "(\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ i) \<in> Y_measure \<rightarrow>\<^sub>M borel"
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
        unfolding Y_measure_def
        by (measurable, use \<open>i < card L\<close> in \<open>auto intro: from_nat_into simp: Vs_enum_inv_from_nat_into_L\<close>)
    qed simp
  next
    case 2
    show ?case
      apply (subst restrict_restrict_space)
      using g_borel
      unfolding comp_def
        apply measurable
      subgoal
        using \<open>i < n\<close> apply (auto elim!: Vs_enum_inv_rightE) sorry
      subgoal by measurable
      done
  qed
qed measurable

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
  assumes "\<And>i. i \<in> L \<Longrightarrow> 0 \<le> Y i"
  assumes "\<And>i. i \<in> L \<Longrightarrow> Y i \<le> 1"
  shows "($) (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}"
  using assms F_gt_0
  unfolding dual_sol_def
  apply (auto intro!: g_nonnegI g_less_eq_OneI)
         apply (metis Vs_enum_inv_def card.empty from_nat_into not_less_zero)
        apply (metis Vs_enum_inv_def card.empty from_nat_into not_less_zero)
       apply (metis Vs_enum_inv_def card.empty from_nat_into not_less_zero)
     apply (metis Vs_enum_inv_def card.empty from_nat_into not_less_zero)
\<comment> \<open>need that ranking produces bipartite matching\<close>
  sorry

lemma dual_sol_from_to_imp:
  shows "Y \<in> L \<rightarrow> {0..1} \<Longrightarrow> ($) (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}"
  by (intro dual_sol_from_to) auto

lemma AE_Y_measure_from_to:
  shows "AE Y in Y_measure. Y \<in> L \<rightarrow> {0..1}"
  unfolding Y_measure_def
  using finite_L
  by (intro AE_PiM_uniform_measure_PiE_countable)
     (auto intro: countable_finite)

lemma AE_dual_sol_from_to:
  shows "AE Y in Y_measure. ($) (dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>)) \<in> {0..<n} \<rightarrow> {0..1/F}" 
  by (rule eventually_mono[OF AE_Y_measure_from_to dual_sol_from_to_imp])
  
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
  have "\<integral>\<^sup>+ x. ennreal (dual_sol x (ranking (linorder_from_keys L x) G \<pi>) $ i) \<partial>Y_measure \<le>
    \<integral>\<^sup>+ x. 1/F \<partial>Y_measure"
    by (rule nn_integral_mono_AE, rule eventually_mono[OF AE_dual_sol_from_to], use 3 in auto)

  also have "\<dots> = 1/F"
    by (simp add: emeasure_space_1)

  finally show ?case
    by (simp add: order_le_less_trans)
qed simp

lemma dual_expectation_feasible_edge:
  assumes "i \<in> L"
  assumes "j \<in> R"
  assumes "{i,j} \<in> G"

shows "expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum i)) +
  expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum j)) \<ge> 1"
  (is "?Ei_plus_Ej \<ge> 1")
proof -
  from \<open>{i,j} \<in> G\<close> have "?Ei_plus_Ej = expectation (\<lambda>Y. dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum i) +
    dual_sol Y (ranking (linorder_from_keys L Y) G \<pi>) $ (Vs_enum j))"
    by (intro Bochner_Integration.integral_add[symmetric] integrable_dual_component)
       (auto dest: edges_are_Vs intro: Vs_enum_less_n)

  show ?thesis
    sorry
qed

end

end