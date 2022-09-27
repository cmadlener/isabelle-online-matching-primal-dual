theory AdWords
  imports 
    Bipartite_Matching_LP
    More_Lattices_Big
    "HOL-Combinatorics.Multiset_Permutations"
begin

sledgehammer_params [provers = cvc4 vampire verit e spass z3 zipperposition]

lemma finite_image_set2':
  assumes "finite {(x,y). P x y}"
  shows "finite {f x y| x y. P x y}"
proof -
  have "{f x y| x y. P x y} = (\<lambda>(x,y). f x y) ` {(x,y). P x y}"
    by auto

  also from assms have "finite \<dots>"
    by blast

  finally show "finite {f x y| x y. P x y}" .
qed


record 'a adwords_state =
  matching :: "'a graph"
  charge :: "'a \<Rightarrow> real"
  x :: "'a \<Rightarrow> real"
  z :: "'a \<Rightarrow> real"

locale adwords_lp = bipartite_matching_lp +
  fixes B :: "'a \<Rightarrow> real"
  fixes b :: "'a set \<Rightarrow> real"
  fixes \<pi> :: "'a list"

  assumes perm: "\<pi> \<in> permutations_of_set R"

  assumes budgets_pos: "\<And>i. i \<in> L \<Longrightarrow> B i > 0"
  assumes bids_pos: "\<And>e. e \<in> G \<Longrightarrow> b e > 0"

  assumes graph_non_empty[intro]: "G \<noteq> {}"
begin

lemma 
  shows L_non_empty[intro,simp]: "L \<noteq> {}"
    and R_non_empty[intro,simp]: "R \<noteq> {}"
  using bipartite_edgeE bipartite_graph graph_non_empty by blast+

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

abbreviation bids_vec :: "real vec" where
  "bids_vec \<equiv> vec m (\<lambda>i. b (from_nat_into G i))"

definition budget_constraint_mat :: "real mat" where
  "budget_constraint_mat \<equiv> mat (card L) m (\<lambda>(i,j). b (from_nat_into G j) * of_bool (from_nat_into L i \<in> from_nat_into G j))"

definition budget_constraint_vec :: "real vec" where
  "budget_constraint_vec \<equiv> vec (card L) (\<lambda>i. B (from_nat_into L i))"

definition matching_constraint_mat :: "real mat" where
  "matching_constraint_mat \<equiv> mat (card R) m (\<lambda>(i,j). of_bool (from_nat_into R i \<in> from_nat_into G j))"

definition constraint_matrix :: "real mat" where
  "constraint_matrix \<equiv> budget_constraint_mat @\<^sub>r matching_constraint_mat"

definition constraint_vec :: "real vec" where
  "constraint_vec \<equiv> budget_constraint_vec @\<^sub>v 1\<^sub>v (card R)"

definition offline_dual :: "'a adwords_state \<Rightarrow> real vec" where
  "offline_dual s \<equiv> vec (card L) (\<lambda>i. x s (from_nat_into L i))"

definition online_dual :: "'a adwords_state \<Rightarrow> real vec" where
  "online_dual s \<equiv> vec (card R) (\<lambda>i. z s (from_nat_into R i))"

definition dual_sol :: "'a adwords_state \<Rightarrow> real vec" where
  "dual_sol s \<equiv> offline_dual s @\<^sub>v online_dual s"

lemma max_value_matchingD: "max_value_matching M \<Longrightarrow> feasible_matching M"
  unfolding max_value_matching_def by blast

lemma 
  shows dim_row_budget_constraint_mat[simp]: "dim_row budget_constraint_mat = card L"
    and  budget_constraint_carrier_mat[intro]: "budget_constraint_mat \<in> carrier_mat (card L) m"
  unfolding budget_constraint_mat_def
  by simp_all

lemma 
  shows dim_budget_constraint_vec[simp]: "dim_vec budget_constraint_vec = card L"
    and budget_constraint_vec_carrier_vec[intro]: "budget_constraint_vec \<in> carrier_vec (card L)"
  unfolding budget_constraint_vec_def by simp_all

lemma 
  shows dim_row_matching_constraint_mat[simp]: "dim_row matching_constraint_mat = card R"
    and matching_constraint_carrier_mat[intro]: "matching_constraint_mat \<in> carrier_mat (card R) m"
  unfolding matching_constraint_mat_def by simp_all

lemma 
  shows constraint_matrix_carrier_mat[intro]: "constraint_matrix \<in> carrier_mat n m"
    and dim_row_constraint_matrix[simp]: "dim_row constraint_matrix = n"
    and dim_col_constraint_matrix[simp]: "dim_col constraint_matrix = m"
  unfolding constraint_matrix_def
  by (auto intro: carrier_matD simp: n_sum)

lemma 
  shows dim_constraint_vec[simp]: "dim_vec constraint_vec = n"
    and constraint_vec_carrier_vec[intro]: "constraint_vec \<in> carrier_vec n"
  unfolding constraint_vec_def
  by (auto simp: n_sum)

lemma 
  shows dim_offline_dual[simp]: "dim_vec (offline_dual s) = card L"
    and offline_dual_carrier_vec[intro]: "offline_dual s \<in> carrier_vec (card L)"
  unfolding offline_dual_def by simp_all

lemma 
  shows dim_online_dual[simp]: "dim_vec (online_dual s) = card R"
    and online_dual_carrier_vec[intro]: "online_dual s \<in> carrier_vec (card R)"
  unfolding online_dual_def by simp_all

lemma
  shows dim_dual_sol[simp]: "dim_vec (dual_sol s) = n"
    and dual_sol_carrier_vec[intro]: "dual_sol s \<in> carrier_vec n"
  unfolding dual_sol_def
  by (auto simp: n_sum)

lemma dual_sol_init[simp]:
  "dual_sol \<lparr> matching = M, charge = f, x = \<lambda>_. 0, z = \<lambda>_. 0 \<rparr> = 0\<^sub>v n"
  unfolding dual_sol_def offline_dual_def online_dual_def append_vec_def
  by (auto simp: Let_def n_sum)

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

definition "R_max \<equiv> Max {b {i, j} / B i | i j. {i,j} \<in> G \<and> i \<in> L \<and> j \<in> R}"
definition "c \<equiv> (1 + R_max) powr (1 / R_max)"

definition adwords_step :: "'a adwords_state \<Rightarrow> 'a \<Rightarrow> 'a adwords_state" where
  "adwords_step s j \<equiv> 
    let ns = {i. {i,j} \<in> G} in
    if ns \<noteq> {} \<and> j \<notin> Vs (matching s)
    then let i = arg_max_on (\<lambda>i. b {i, j} * (1 - (x s) i)) ns in
      if (x s) i \<ge> 1 
      then s
      else \<lparr> 
        matching = insert {i,j} (matching s),
        charge = (charge s)(i := min (b {i, j}) (B i - (charge s) i)),
        x = (x s)(i := (x s) i * (1 + b {i, j} / B i) + b {i, j} / ((c-1) * B i)),
        z = (z s)(j := b {i, j} * (1 - (x s) i))
      \<rparr>
    else s"

definition "adwords' s \<equiv> foldl adwords_step s"
abbreviation "adwords \<equiv> adwords' \<lparr> matching = {}, charge = \<lambda>_. 0, x = \<lambda>_. 0, z = \<lambda>_. 0 \<rparr>"

lemma adwords_Nil[simp]: "adwords' s [] = s"
  unfolding adwords'_def by simp

lemma adwords_Cons: "adwords' s (j#js) = adwords' (adwords_step s j) js"
  unfolding adwords'_def by simp

lemma adwords_append: "adwords' s (js@js') = adwords' (adwords' s js) js'"
  unfolding adwords'_def by simp

lemma adwords_step_cases[case_names no_neighbor j_matched no_budget new_match]:
  fixes j s
  defines "i \<equiv> arg_max_on (\<lambda>i. b {i,j} * (1 - x s i)) {i. {i,j} \<in> G}"

  assumes "{i. {i,j} \<in> G} = {} \<Longrightarrow> P"
  assumes "j \<in> Vs (matching s) \<Longrightarrow> P"
  assumes "x s i \<ge> 1 \<Longrightarrow> P"
  assumes "\<lbrakk> {i. {i,j} \<in> G} \<noteq> {}; j \<notin> Vs (matching s);
    i \<in> {i. {i,j} \<in> G}; x s i < 1;
    \<not>(\<exists>i'\<in>{i. {i,j} \<in> G}. b {i',j} * (1 - x s i') > b {i,j} * (1 - x s i)) \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  consider "{i. {i,j} \<in> G} = {}" | "j \<in> Vs (matching s)" | "x s i \<ge> 1" | "{i. {i,j} \<in> G} \<noteq> {} \<and> j \<notin> Vs (matching s) \<and> x s i < 1"
    by fastforce

  then show P
  proof cases
    case 4
    then have "i \<in> {i. {i,j} \<in> G} \<and> \<not>(\<exists>i'\<in>{i. {i,j} \<in> G}. b {i',j} * (1 - x s i') > b {i,j} * (1 - x s i))"
      unfolding i_def
      by (intro conjI arg_max_if_finite)
         (auto intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

    with 4 assms show P
      by blast
  qed (use assms in auto)
qed

lemma R_max_pos: "0 < R_max"
  unfolding R_max_def
  apply (subst Max_gr_iff)
    apply (rule finite_image_set2')
    apply (rule finite_subset[where B = "Vs G \<times> Vs G"])
  subgoal
    apply (auto dest: edges_are_Vs)
    done
  subgoal
    by blast
  subgoal
    using bipartite_graph graph_non_empty
    apply auto
    by (metis bipartite_edgeE)
  subgoal
    using graph_non_empty
    apply (auto)
    by (metis bids_pos bipartite_edgeE bipartite_graph budgets_pos divide_pos_pos)
  done

lemma c_gt_1: "1 < c"
  unfolding c_def
  using R_max_pos
  by auto

lemma adwords_step_x_mono:
  assumes "0 \<le> x s i"
  assumes "j \<in> R"
  shows "x s i \<le> x (adwords_step s j) i"
proof (cases j rule: adwords_step_cases[where s = s])
  case new_match
  let ?i' = "arg_max_on (\<lambda>i. b {i,j} * (1 - x s i)) {i. {i,j} \<in> G}"

  show ?thesis
  proof (cases "?i' = i")
    case True

    from new_match bipartite_graph \<open>j \<in> R\<close> have "?i' \<in> L"
      by (auto dest: bipartite_edgeD)

    with new_match \<open>0 \<le> x s i\<close> have "x s i \<le> x s i * (1 + b {i, j} / B i)"
      by (auto simp: mult_le_cancel_left1 True dest!: budgets_pos bids_pos)

    also from new_match c_gt_1 \<open>?i' \<in> L\<close> have "\<dots> \<le> x s i * (1 + b {i,j} / B i) + b {i,j} / ((c-1) * B i)"
      by (auto simp: True dest!: budgets_pos bids_pos)

    finally show ?thesis
      by (auto simp: True adwords_step_def)
  next
    case False
    with new_match show ?thesis
      by (auto simp: adwords_step_def Let_def)
  qed
qed (simp_all add: adwords_step_def)

lemma adwords_x_mono:
  assumes "0 \<le> x s i"
  assumes "set js \<subseteq> R"
  shows "x s i \<le> x (adwords' s js) i"
  using assms
proof (induction js arbitrary: s)
  case (Cons j js)
  then have "x s i \<le> x (adwords_step s j) i"
    by (auto intro: adwords_step_x_mono)

  also with Cons.prems have "\<dots> \<le> x (adwords' (adwords_step s j) js) i"
    by (auto intro: Cons.IH)

  finally show ?case
    by (simp add: adwords_Cons)    
qed simp

lemma adwords_x_nonneg: "set js \<subseteq> R \<Longrightarrow> 0 \<le> x s i \<Longrightarrow> 0 \<le> x (adwords' s js) i"
  using adwords_x_mono by fastforce

lemma adwords_step_z_nonneg:
  assumes "0 \<le> z s i"
  shows "z (adwords_step s j) i \<ge> 0"
proof (cases j rule: adwords_step_cases[where s = s])
  case new_match
  with assms show ?thesis
    by (auto simp: adwords_step_def Let_def intro: mult_nonneg_nonneg dest: bids_pos)
qed (use assms in \<open>simp_all add: adwords_step_def\<close>)

lemma adwords_z_nonneg: "0 \<le> z s i \<Longrightarrow> z (adwords' s js) i \<ge> 0"
  by (induction js arbitrary: s)
     (auto simp: adwords_Cons dest: adwords_step_z_nonneg)

lemma adwords_step_z_unchanged:
  assumes "j \<noteq> j'"
  shows "z (adwords_step s j') j = z s j"
  using assms
  by (cases j' rule: adwords_step_cases[where s = s])
     (auto simp: adwords_step_def Let_def)

lemma adwords_z_unchanged:
  assumes "j \<notin> set js"
  shows "z (adwords' s js) j = z s j"
  using assms
  by (induction js arbitrary: s)
     (auto simp: adwords_Cons dest: adwords_step_z_unchanged)

lemma arg_max_in_L:
  fixes f :: "'a \<Rightarrow> 'b::order"
  assumes "j \<in> R"
  assumes "{i. {i,j} \<in> G} \<noteq> {}"
  shows "arg_max_on f {i. {i,j} \<in> G} \<in> L"
proof -
  from assms have "arg_max_on f {i. {i,j} \<in> G} \<in> {i. {i,j} \<in> G}"
    by (intro arg_max_if_finite)
       (auto intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

  with bipartite_graph \<open>j \<in> R\<close> show ?thesis
    by (auto dest: bipartite_edgeD)
qed

lemma unmatched_R_in_adwords_step_if:
  assumes "j \<in> R" "j' \<in> R"
  assumes "j \<noteq> j'"
  assumes "j \<notin> Vs (matching s)"
  shows "j \<notin> Vs (matching (adwords_step s j'))"
  using assms bipartite_graph
  by (cases j rule: adwords_step_cases[where s = s])
     (auto simp: adwords_step_def Let_def vs_insert dest: arg_max_in_L)

lemma unmatched_R_in_adwords_if:
  assumes "j \<notin> set js" "j \<in> R"
  assumes "set js \<subseteq> R"
  assumes "j \<notin> Vs (matching s)"
  shows "j \<notin> Vs (matching (adwords' s js))"
  using assms
proof (induction js arbitrary: s)
  case (Cons j' js)

  then have "j \<notin> Vs (matching (adwords_step s j'))"
    by (intro unmatched_R_in_adwords_step_if) auto

  with Cons show ?case
    by (simp add: adwords_Cons)
qed simp

lemma dual_feasible_edge:
  assumes "i \<in> L"
  assumes "j \<in> R"
  assumes "{i,j} \<in> G"

  shows "b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j \<ge> b {i,j}"
proof (cases "x (adwords \<pi>) i \<ge> 1")
  case True
  with \<open>{i,j} \<in> G\<close> have "b {i,j} \<le> b {i,j} * x (adwords \<pi>) i"
    by (auto dest: bids_pos)

  also have "\<dots> \<le> b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j"
    by (auto intro: adwords_z_nonneg)

  finally show ?thesis .
next
  case False

  from perm \<open>j \<in> R\<close> obtain pre suff where \<pi>_decomp: "\<pi> = pre @ j # suff" "j \<notin> set pre" "j \<notin> set suff"
    by (metis permutations_of_setD split_list_distinct)

  with perm have set_pre: "set pre \<subseteq> R" and set_suff: "set suff \<subseteq> R"
    by (auto dest: permutations_of_setD)

  let ?i' = "arg_max_on (\<lambda>i. b {i,j} * (1 - x (adwords pre) i)) {i. {i,j} \<in> G}"

  show ?thesis
  proof (cases j rule: adwords_step_cases[where s = "adwords pre"])
    case no_neighbor
    with \<open>{i,j} \<in> G\<close> show ?thesis by blast
  next
    case j_matched
    from \<pi>_decomp set_pre \<open>j \<in> R\<close> have "j \<notin> Vs (matching (adwords pre))"
      by (intro unmatched_R_in_adwords_if) auto

    with j_matched show ?thesis by blast
  next
    case no_budget

    from \<open>{i,j} \<in> G\<close> have "?i' \<in> {i. {i,j} \<in> G}"
      by (intro arg_max_if_finite)
         (auto intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

    with bipartite_graph \<open>j \<in> R\<close> have "{?i',j} \<in> G"
      by (auto dest: bipartite_edgeD)

    from perm have "x (adwords pre) i \<le> x (adwords \<pi>) i"
      by (auto simp: adwords_append \<pi>_decomp intro!: adwords_x_mono adwords_x_nonneg dest: permutations_of_setD)

    also from False have "\<dots> < 1"
      by simp

    finally have "x (adwords pre) i < 1" .

    with \<open>{i,j} \<in> G\<close> have i_gt_0: "b {i,j} * (1 - x (adwords pre) i) > 0"
      by (auto dest: bids_pos)

    from \<open>{i,j} \<in> G\<close> have i_le_i': "b {i,j} * (1 - x (adwords pre) i) \<le> b {?i',j} * (1 - x (adwords pre) ?i')"
      by (auto intro!: arg_max_greatest intro: finite_subset[where B = "Vs G"] dest: edges_are_Vs)

    have "x (adwords pre) ?i' < 1"
    proof (rule ccontr, simp add: not_less)
      assume "1 \<le> x (adwords pre) ?i'"

      with \<open>{?i',j} \<in> G\<close> have "b {?i',j} * (1 - x (adwords pre) ?i') \<le> 0"
        by (auto dest: bids_pos simp: field_simps)

      with i_gt_0 i_le_i' show False
        by linarith
    qed

    with no_budget show ?thesis by simp
  next
    case new_match
    with \<open>{i,j} \<in> G\<close> have z_step: "z (adwords_step (adwords pre) j) j = b {?i',j} * (1 - x (adwords pre) ?i')"
      by (auto simp: adwords_step_def Let_def)

    have "b {i,j} = b {i,j} * x (adwords pre) i + b {i,j} * (1 - x (adwords pre) i)"
      by argo

    also from set_pre set_suff \<open>{i,j} \<in> G\<close> \<open>j \<in> R\<close> have "\<dots> \<le> b {i,j} * x (adwords \<pi>) i + b {i,j} * (1 - x (adwords pre) i)"
      apply (auto dest!: bids_pos simp: \<pi>_decomp adwords_append intro!: adwords_x_mono adwords_x_nonneg)
      apply blast
      done      

    also from new_match \<open>{i,j} \<in> G\<close>
    have "\<dots> \<le> b {i,j} * x (adwords \<pi>) i + b {?i',j} * (1 - x (adwords pre) ?i')"
      by fastforce

    also from \<open>j \<notin> set suff\<close> have "\<dots> = b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j"
      by (auto simp: \<pi>_decomp adwords_append adwords_Cons adwords_z_unchanged z_step)

    finally show ?thesis .
  qed
qed

lemma dual_feasible:
  shows "constraint_matrix\<^sup>T *\<^sub>v dual_sol (adwords \<pi>) \<ge> bids_vec"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, simp_all)
  fix k assume "k < m"

  then have col_k: "col constraint_matrix k = col budget_constraint_mat k @\<^sub>v col matching_constraint_mat k"
    unfolding constraint_matrix_def append_rows_def
    by (auto intro!: col_four_block_mat)

  from \<open>k < m\<close> have col_carrier_vec[intro]: "col budget_constraint_mat k \<in> carrier_vec (card L)" "col matching_constraint_mat k \<in> carrier_vec (card R)"
    by (auto intro: col_carrier_vec)
    
  from \<open>k < m\<close> obtain i j where ij: "{i,j} \<in> G" "from_nat_into G k = {i,j}" "i \<in> L" "j \<in> R"
    by (auto elim: from_nat_into_G_E)

  then have [simp]: "from_nat_into L (to_nat_on L i) = i" "from_nat_into R (to_nat_on R j) = j"
    by simp_all

  from \<open>i \<in> L\<close> \<open>j \<in> R\<close> have indicat_online: "{0..<card R} \<inter> {l. from_nat_into R l \<in> from_nat_into G k} = {to_nat_on R j}"
    by (auto simp: \<open>from_nat_into G k = {i,j}\<close> from_nat_into R_enum_less_card)

  from \<open>k < m\<close> have [simp]: "col matching_constraint_mat k \<bullet> online_dual (adwords \<pi>) = z (adwords \<pi>) j"
    unfolding matching_constraint_mat_def online_dual_def scalar_prod_def
    by (auto simp: indicat_online)

  from from_nat_into[OF L_non_empty] \<open>i \<in> L\<close> \<open>j \<in> R\<close> have indicat_offline: "{0..<card L} \<inter> {i. from_nat_into L i \<in> from_nat_into G k} = {to_nat_on L i}"
    by (auto simp: \<open>from_nat_into G k = {i,j}\<close> L_enum_less_card)

  from \<open>k <  m\<close> have [simp]: "col budget_constraint_mat k \<bullet> offline_dual (adwords \<pi>) = b {i,j} * x (adwords \<pi>) i"
    unfolding budget_constraint_mat_def offline_dual_def scalar_prod_def
    by (auto simp: ac_simps indicat_offline simp flip: sum_distrib_left intro: arg_cong[OF ij(2)])

  from ij have "b (from_nat_into G k) \<le> b {i,j} * x (adwords \<pi>) i + z (adwords \<pi>) j"
    by (auto intro: dual_feasible_edge)

  also from \<open>k < m\<close> have "\<dots> = col constraint_matrix k \<bullet> dual_sol (adwords \<pi>)"
    unfolding dual_sol_def
    by (subst col_k, subst scalar_prod_append) auto

  finally show "b (from_nat_into G k) \<le> col constraint_matrix k \<bullet> dual_sol (adwords \<pi>)" .
qed

lemma dual_nonneg:
  "dual_sol (adwords \<pi>) \<ge> 0\<^sub>v n"
  unfolding less_eq_vec_def dual_sol_def online_dual_def offline_dual_def
  using perm
  by (auto simp: n_sum intro: adwords_x_nonneg adwords_z_nonneg dest: permutations_of_setD)

lemma dual_primal_times_adwords_step:
  assumes "j \<in> R"
  assumes "z s j = 0"
  assumes "constraint_vec \<bullet> dual_sol s * (1 - 1 / c) = bids_vec \<bullet> primal_sol (matching s)"
  shows "constraint_vec \<bullet> dual_sol (adwords_step s j) * (1 - 1 / c) = bids_vec \<bullet> primal_sol (matching (adwords_step s j))"
proof (cases j rule: adwords_step_cases[where s = s])
  case new_match
  let ?i = "arg_max_on (\<lambda>i. b {i, j} * (1 - x s i)) {i. {i, j} \<in> G}"

  from new_match bipartite_graph \<open>j \<in> R\<close> have "?i \<in> L"
    by (auto dest: bipartite_edgeD)

  from new_match 
  have matching_insert: "matching (adwords_step s j) = insert {?i,j} (matching s)"
    and edge: "{?i,j} \<in> G"
    and x_upd: "x (adwords_step s j) = (x s)(?i := (x s) ?i * (1 + b {?i, j} / B ?i) + b {?i, j} / ((c-1) * B ?i))"
    and z_upd: "z (adwords_step s j) = (z s)(j := b {?i, j} * (1 - (x s) ?i))"
    by (simp_all add: adwords_step_def Let_def)

  from new_match have "{?i,j} \<notin> matching s"
    by (auto dest: edges_are_Vs)

  with edge have insert_indices: "{0..<m} \<inter> {i. from_nat_into G i \<in> matching (adwords_step s j)} = 
    insert (G_enum {?i,j}) ({0..<m} \<inter> {i. from_nat_into G i \<in> matching s})"
    apply (auto simp: matching_insert countable_finite intro: G_enum_less_m)
    apply (metis finite_graph m_def to_nat_on_from_nat_into_less)
    done

  from \<open>{?i,j} \<notin> matching s\<close> have "G_enum {?i,j} \<notin> ({0..<m} \<inter> {i. from_nat_into G i \<in> matching s})"
    by (auto simp: countable_finite edge)

  then have \<Delta>_primal: "bids_vec \<bullet> primal_sol (matching (adwords_step s j)) = b {?i,j} + bids_vec \<bullet> primal_sol (matching s)"
    by (auto simp: scalar_prod_def primal_sol_def insert_indices countable_finite edge)

  have \<Delta>_offline: "budget_constraint_vec \<bullet> offline_dual (adwords_step s j) = B ?i * (x s ?i * b {?i,j} / B ?i + b {?i,j} / ((c-1) * B ?i)) +
    budget_constraint_vec \<bullet> offline_dual s" (is "?B' = ?\<Delta> + ?B")
  proof -
    from \<open>?i \<in> L\<close> have "to_nat_on L ?i < card L"
      by (auto intro: L_enum_less_card)

    with \<open>?i \<in> L\<close> have "?B' = B ?i * x (adwords_step s j) ?i + (\<Sum>i\<in>{0..<card L} - {to_nat_on L ?i}. B (from_nat_into L i) * x (adwords_step s j) (from_nat_into L i))"
      unfolding budget_constraint_vec_def offline_dual_def scalar_prod_def
      by (auto simp: sum.remove[where x = "to_nat_on L ?i"])

    also have "\<dots> = B ?i * (x s ?i * (1 + b {?i, j} / B ?i) + b {?i, j} / ((c-1) * B ?i)) +
      (\<Sum>i\<in>{0..<card L} - {to_nat_on L ?i}. B (from_nat_into L i) * x s (from_nat_into L i))"
      apply (rule arg_cong2[where f= plus])
       apply (auto simp add: x_upd intro!: sum.cong split: if_splits)
      by (metis L_enum_inv)

    also have "\<dots> = B ?i * (x s ?i * b {?i,j} / B ?i + b {?i,j} / ((c-1) * B ?i)) + B ?i * x s ?i +
      (\<Sum>i\<in>{0..<card L} - {to_nat_on L ?i}. B (from_nat_into L i) * x s (from_nat_into L i))"
      by (auto simp: field_simps)

    also from \<open>?i \<in> L\<close> \<open>to_nat_on L ?i < card L\<close> have "\<dots> = ?\<Delta> +
      (\<Sum>i\<in>{0..<card L}. B (from_nat_into L i) * x s (from_nat_into L i))"
      by (auto simp: sum.remove[where x = "to_nat_on L ?i"])

    finally show ?thesis
      unfolding budget_constraint_vec_def offline_dual_def scalar_prod_def
      by simp
  qed

  from \<open>j \<in> R\<close> have *: "{0..<card R} \<inter> {i. from_nat_into R i = j} = {to_nat_on R j}"
    by (auto intro: R_enum_less_card)

  from \<open>j \<in> R\<close> have **: "{0..<card R} \<inter> - {i. from_nat_into R i = j} = {0..<card R} - {to_nat_on R j}"
    by auto

  from \<open>z s j = 0\<close> \<open>j \<in> R\<close> have \<Delta>_online: "1\<^sub>v (card R) \<bullet> online_dual (adwords_step s j) = b {?i,j} * (1 - x s ?i) + 1\<^sub>v (card R) \<bullet> online_dual s"
    unfolding scalar_prod_def online_dual_def
    apply (auto simp: z_upd sum.If_cases * **)
    apply (subst (2) sum.remove[where x = "to_nat_on R j"])
      apply (auto intro: R_enum_less_card)
    done

  have "constraint_vec \<bullet> dual_sol (adwords_step s j) = budget_constraint_vec \<bullet> offline_dual (adwords_step s j) +
    1\<^sub>v (card R) \<bullet> online_dual (adwords_step s j)"
    unfolding constraint_vec_def dual_sol_def
    by (auto intro!: scalar_prod_append)

  also have "\<dots> = ?\<Delta> + ?B + b {?i,j} * (1 - x s ?i) + 1\<^sub>v (card R) \<bullet> online_dual s"
    by (simp add: \<Delta>_offline \<Delta>_online)

  also have "\<dots> = ?\<Delta> + b {?i,j} * (1 - x s ?i) + constraint_vec \<bullet> dual_sol s"
    unfolding constraint_vec_def dual_sol_def
    by (auto intro!: scalar_prod_append[symmetric])

  finally have \<Delta>_dual: "constraint_vec \<bullet> dual_sol (adwords_step s j) = 
    ?\<Delta> + b {?i,j} * (1 - x s ?i) + constraint_vec \<bullet> dual_sol s" .

  have "\<dots> * (1 - 1/c) = (?\<Delta> + b {?i,j} * (1 - x s ?i)) * (1 - 1/c) + bids_vec \<bullet> primal_sol (matching s)"
    by (auto simp: field_simps assms)

  also from c_gt_1 \<open>?i \<in> L\<close> have "\<dots> = b {?i,j} + bids_vec \<bullet> primal_sol (matching s)"
    by (auto simp: field_simps dest: budgets_pos)

  finally show ?thesis 
    by (auto simp flip: \<Delta>_primal simp: \<Delta>_dual)
qed (use assms in \<open>auto simp: adwords_step_def\<close>)

lemma dual_primal_times_adwords':
  assumes "constraint_vec \<bullet> dual_sol s * (1 - 1 / c) = bids_vec \<bullet> primal_sol (adwords_state.matching s)"
  assumes "distinct js"
  assumes "set js \<subseteq> R"
  assumes "\<forall>j \<in> set js. z s j = 0"
  shows "constraint_vec \<bullet> dual_sol (adwords' s js) * (1 - 1 / c) = bids_vec \<bullet> primal_sol (matching (adwords' s js))"
  using assms
proof (induction js arbitrary: s)
  case (Cons j js)

  then have step: "constraint_vec \<bullet> dual_sol (adwords_step s j) * (1 - 1/c) = bids_vec \<bullet> primal_sol (matching (adwords_step s j))"
    by (auto intro: dual_primal_times_adwords_step)

  from Cons.prems have "\<forall>j' \<in> set js. z (adwords_step s j) j' = z s j'"
    by (intro ballI adwords_step_z_unchanged) auto

  with Cons.prems have "\<forall>j' \<in> set js. z (adwords_step s j) j' = 0"
    by simp

  with Cons step show ?case
    by (auto simp: adwords_Cons)
qed simp

lemma dual_primal_times_adwords:
  shows "constraint_vec \<bullet> dual_sol (adwords \<pi>) * (1 - 1/c) = bids_vec \<bullet> primal_sol (matching (adwords \<pi>))"
  using perm c_gt_1
  by (auto intro!: dual_primal_times_adwords' scalar_prod_right_zero dest: permutations_of_setD)

end

end
