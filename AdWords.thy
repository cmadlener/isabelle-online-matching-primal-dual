theory AdWords
  imports Bipartite_Matching_LP
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]


record 'a adwords_state =
  matching :: "'a graph"
  charge :: "'a \<Rightarrow> real"
  x :: "'a \<Rightarrow> real"
  z :: "'a \<Rightarrow> real"

locale adwords_lp = bipartite_matching_lp +
  fixes B :: "'a \<Rightarrow> real"
  fixes b :: "'a set \<Rightarrow> real"

  assumes budgets_pos: "\<And>i. i \<in> L \<Longrightarrow> B i > 0"
  assumes weights_pos: "\<And>e. e \<in> G \<Longrightarrow> b e > 0"
begin

abbreviation "matching_value M \<equiv> \<Sum>e\<in>M. b e"
abbreviation "charge_of M i \<equiv> \<Sum>e\<in>{e \<in> M. i \<in> e}. b e"

definition "feasible_matching M \<longleftrightarrow> one_sided_matching G M R \<and>
  (\<forall>i \<in> L. charge_of M i \<le> B i)"

lemma feasible_matchingI:
  assumes "one_sided_matching G M R"
  assumes "\<And>i. i \<in> L \<Longrightarrow> charge_of M i \<le> B i"
  shows "feasible_matching M"
  unfolding feasible_matching_def
  using assms
  by blast

lemma feasible_matching_one_sidedD:
  "feasible_matching M \<Longrightarrow> one_sided_matching G M R"
  unfolding feasible_matching_def by blast

lemma feasible_matching_chargeD:
  assumes "feasible_matching M"
  assumes "i \<in> L"
  shows "charge_of M i \<le> B i"
  using assms
  unfolding feasible_matching_def
  by blast

definition "max_value_matching M \<longleftrightarrow> feasible_matching M \<and>
  (\<forall>M'. feasible_matching M \<longrightarrow> matching_value M' \<le> matching_value M)"

lemma max_value_matchingD: "max_value_matching M \<Longrightarrow> feasible_matching M"
  unfolding max_value_matching_def by blast

abbreviation bids_vec :: "real vec" where
  "bids_vec \<equiv> vec m (\<lambda>i. b (from_nat_into G i))"

definition budget_constraint_mat :: "real mat" where
  "budget_constraint_mat \<equiv> mat (card L) m (\<lambda>(i,j). b (from_nat_into G j) * of_bool (from_nat_into L i \<in> from_nat_into G j))"

lemma dim_row_budget_constraint_mat[simp]: "dim_row budget_constraint_mat = card L"
  unfolding budget_constraint_mat_def by simp

lemma budget_constraint_carrier_mat[intro]: "budget_constraint_mat \<in> carrier_mat (card L) m"
  unfolding budget_constraint_mat_def
  by simp

definition budget_constraint_vec :: "real vec" where
  "budget_constraint_vec \<equiv> vec (card L) (\<lambda>i. B (from_nat_into L i))"

lemma dim_budget_constraint_vec[simp]: "dim_vec budget_constraint_vec = card L"
  unfolding budget_constraint_vec_def by simp

lemma budget_constraint_vec_carrier_vec[intro]: "budget_constraint_vec \<in> carrier_vec (card L)"
  unfolding budget_constraint_vec_def by simp

definition matching_constraint_mat :: "real mat" where
  "matching_constraint_mat \<equiv> mat (card R) m (\<lambda>(i,j). of_bool (from_nat_into R i \<in> from_nat_into G j))"

lemma dim_row_matching_constraint_mat[simp]: "dim_row matching_constraint_mat = card R"
  unfolding matching_constraint_mat_def by simp

lemma matching_constraint_carrier_mat[intro]: "matching_constraint_mat \<in> carrier_mat (card R) m"
  unfolding matching_constraint_mat_def by simp

definition constraint_matrix :: "real mat" where
  "constraint_matrix \<equiv> budget_constraint_mat @\<^sub>r matching_constraint_mat"

lemma constraint_matrix_carrier_mat[intro]: "constraint_matrix \<in> carrier_mat n m"
  unfolding constraint_matrix_def
  by (auto simp: n_sum)

lemma dim_row_constraint_matrix[simp]: "dim_row constraint_matrix = n"
  by (auto intro: carrier_matD)

definition constraint_vec :: "real vec" where
  "constraint_vec \<equiv> budget_constraint_vec @\<^sub>v 1\<^sub>v (card R)"

lemma dim_constraint_vec[simp]: "dim_vec constraint_vec = n"
  unfolding constraint_vec_def
  by (simp add: n_sum)

lemma constraint_vec_carrier_vec[intro]: "constraint_vec \<in> carrier_vec n"
  unfolding constraint_vec_def
  by (auto simp: n_sum)

lemma primal_dot_bids_eq_value:
  assumes "M \<subseteq> G"
  shows "bids_vec \<bullet> primal_sol M = matching_value M"
  unfolding scalar_prod_def primal_sol_def
  using assms
  by (auto intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = G_enum]
           intro: to_nat_on_from_nat_into_less simp: m_def to_nat_on_less_card countable_finite)

lemma feasible_matching_budget_constraint:
  assumes "feasible_matching M"
  shows "budget_constraint_mat *\<^sub>v primal_sol M \<le> budget_constraint_vec"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, simp_all)
  fix i assume [intro,simp]: "i < card L"

  from assms have "row budget_constraint_mat i \<bullet> primal_sol M = charge_of M (from_nat_into L i)"
    unfolding scalar_prod_def budget_constraint_mat_def primal_sol_def m_def
    by (auto simp:  to_nat_on_from_nat_into_less countable_finite to_nat_on_less_card
             intro!: sum.reindex_bij_witness[where j = "from_nat_into G" and i = G_enum]
             dest!: feasible_matching_one_sidedD one_sided_matching_subgraphD)

  also from assms have "\<dots> \<le> B (from_nat_into L i)"
    by (auto intro: feasible_matching_chargeD  Vs_enum_inv_leftE simp flip: Vs_enum_inv_from_nat_into_L)

  also have "\<dots> = budget_constraint_vec $ i"
    unfolding budget_constraint_vec_def by simp

  finally show "row budget_constraint_mat i \<bullet> primal_sol M \<le> budget_constraint_vec $ i" .
qed

lemma one_sided_matching_matching_constraint:
  assumes "one_sided_matching G M R"
  shows "matching_constraint_mat *\<^sub>v primal_sol M \<le> 1\<^sub>v (card R)"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, simp_all)
  fix i assume [intro,simp]: "i < card R"

  have online: "from_nat_into R i \<in> R"
    by (metis \<open>i < card R\<close> bot_nat_0.extremum_strict card.empty from_nat_into)

  from assms have "row matching_constraint_mat i \<bullet> primal_sol M = card {e\<in>M. (from_nat_into R i \<in> e)}"
    unfolding scalar_prod_def matching_constraint_mat_def primal_sol_def m_def
    by (auto intro!: bij_betw_same_card[where f = "from_nat_into G"] bij_betwI[where g = G_enum]
                     to_nat_on_less_card 
             intro: to_nat_on_from_nat_into_less
             dest: one_sided_matching_subgraphD'
             simp: countable_finite)

  also from assms online have "\<dots> \<le> 1"
    unfolding one_sided_matching_def
    by auto

  finally show "row matching_constraint_mat i \<bullet> primal_sol M \<le> 1" .
qed

lemma feasible_matching_feasible:
  assumes "feasible_matching M"
  shows "constraint_matrix *\<^sub>v primal_sol M \<le> constraint_vec"
  unfolding constraint_matrix_def constraint_vec_def
  by (subst append_rows_le)
     (use assms in \<open>auto intro: feasible_matching_budget_constraint one_sided_matching_matching_constraint 
                         dest: feasible_matching_one_sidedD\<close>)

lemma budget_constraint_feasible:
  assumes "M \<subseteq> G"
  assumes "budget_constraint_mat *\<^sub>v primal_sol M \<le> budget_constraint_vec"
  assumes "i \<in> L"
  shows "charge_of M i \<le> B i"
proof -
  from \<open>i \<in> L\<close> have index: "to_nat_on L i < card L"
    using L_enum_less_card by blast

  with \<open>M \<subseteq> G\<close> \<open>i \<in> L\<close> have "charge_of M i = (budget_constraint_mat *\<^sub>v primal_sol M) $ to_nat_on L i"
    unfolding mult_mat_vec_def scalar_prod_def budget_constraint_mat_def primal_sol_def
    by (auto intro!: sum.reindex_bij_witness[where j = G_enum and i = "from_nat_into G"]
             simp: countable_finite m_def to_nat_on_less_card to_nat_on_from_nat_into_less)

  also from assms index have "\<dots> \<le> B i"
    unfolding less_eq_vec_def budget_constraint_vec_def
    by auto

  finally show "charge_of M i \<le> B i" .
qed

lemma matching_constraint_one_sided_matching:
  assumes "M \<subseteq> G"
  assumes "matching_constraint_mat *\<^sub>v primal_sol M \<le> 1\<^sub>v (card R)"
  shows "one_sided_matching G M R"
proof (intro one_sided_matchingI)
  fix j assume "j \<in> R"

  then have index: "to_nat_on R j < card R"
    using R_enum_less_card by blast

  from \<open>M \<subseteq> G\<close> have "finite M"
    by (auto intro: finite_subset)

  with index \<open>M \<subseteq> G\<close> \<open>j \<in> R\<close> have 
    "card {e \<in> M. j \<in> e} = (matching_constraint_mat *\<^sub>v primal_sol M) $ to_nat_on R j"
    unfolding mult_mat_vec_def scalar_prod_def matching_constraint_mat_def primal_sol_def
    by (auto intro!: bij_betw_same_card[where f = G_enum] bij_betwI[where g = "from_nat_into G"]
             simp: Int_def m_def to_nat_on_less_card to_nat_on_from_nat_into_less countable_finite)

  also from index assms have "\<dots> \<le> 1"
    unfolding less_eq_vec_def
    by auto

  finally show "card {e \<in> M. j \<in> e} \<le> 1"
    by simp
qed (use assms in simp)

lemma feasible_feasible_matching:
  assumes "M \<subseteq> G"
  assumes "constraint_matrix *\<^sub>v primal_sol M \<le> constraint_vec"
  shows "feasible_matching M"
  using assms
  unfolding constraint_matrix_def constraint_vec_def
  by (subst (asm) append_rows_le)
     (auto intro: feasible_matchingI matching_constraint_one_sided_matching budget_constraint_feasible)

lemma feasible_matching_iff_feasible:
  assumes "M \<subseteq> G"
  shows "feasible_matching M \<longleftrightarrow> constraint_matrix *\<^sub>v primal_sol M \<le> constraint_vec"
  using assms
  by (auto intro: feasible_matching_feasible feasible_feasible_matching)

lemma matching_value_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "feasible_matching M"

  assumes "constraint_matrix\<^sup>T *\<^sub>v y \<ge> bids_vec"
  assumes "y \<ge> 0\<^sub>v n"

  shows "matching_value M \<le> constraint_vec \<bullet> y"
proof -
  from assms have "matching_value M = bids_vec \<bullet> primal_sol M"
    by (auto simp: primal_dot_bids_eq_value dest!: feasible_matching_one_sidedD one_sided_matching_subgraphD)

  also from assms have "\<dots> \<le> constraint_vec \<bullet> y"
    by (auto intro: weak_duality_theorem_nonneg_primal[where A = constraint_matrix] feasible_matching_feasible)

  finally show ?thesis .
qed

lemma max_value_matching_bound_by_feasible_dual:
  fixes y :: "real vec"
  assumes "max_value_matching M"

  assumes "constraint_matrix\<^sup>T *\<^sub>v y \<ge> bids_vec"
  assumes "y \<ge> 0\<^sub>v n"

  shows "matching_value M \<le> constraint_vec \<bullet> y"
  using assms
  by (auto intro: matching_value_bound_by_feasible_dual dest: max_value_matchingD)

end

end
