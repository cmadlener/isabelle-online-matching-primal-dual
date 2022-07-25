theory Ranking_Primal_Dual_Probabilistic
  imports
    Ranking_Primal_Dual
    "Treaps.Random_List_Permutation"
begin

hide_const Finite_Cartesian_Product.vec Inner_Product.real_inner_class.inner
hide_fact less_eq_vec_def

lemma carrier_vec_0: "carrier_vec 0 = {vec 0 f}"
  by auto

lemma card_carrier_vec_0[simp]: "card (carrier_vec 0) = 1"
  using carrier_vec_0
  by (simp add: card_Suc_eq) blast

lemma card_carrier_vec_finite:
  assumes "finite F"
  shows "card {v \<in> carrier_vec n. \<forall>i<n. v $ i \<in> F} = card F ^ n" (is "card ?A = _")
proof -
  let ?B = "{xs. set xs \<subseteq> F \<and> length xs = n}"

  have "card ?A = card ?B"
  proof (intro bij_betw_same_card[where f = "list_of_vec"], unfold bij_betw_def, auto)
    show "inj_on list_of_vec {v \<in> carrier_vec n. \<forall>i<n. v $ i \<in> F}"
      by (intro inj_onI) (metis vec_list)
  next
    fix v x
    assume "v \<in> carrier_vec n" "\<forall>i<n. v $ i \<in> F" "x \<in> set (list_of_vec v)"
    then show "x \<in> F"
      by (auto simp: set_list_of_vec dest: carrier_vecD elim: vec_setE)
  next
    fix xs
    assume "set xs \<subseteq> F" "n = length xs"
    then show "xs \<in> list_of_vec ` {v \<in> carrier_vec (length xs). \<forall>i<length xs. v $ i \<in> F}"
      unfolding image_def
      by auto (rule exI[of _ "vec_of_list xs"], auto simp: carrier_dim_vec index_vec_of_list list_vec)
  qed

  also from assms have "\<dots> = card F ^ n"
    by (intro card_lists_length_eq)

  finally show ?thesis .
qed

lemma finite_carrier_vec:
  assumes "finite F"
  shows "finite {v \<in> carrier_vec n. \<forall>i<n. v $ i \<in> F}" (is "finite ?V")
proof -
  from assms have card_eq: "card ?V = card F ^ n"
    by (rule card_carrier_vec_finite)

  with assms show ?thesis
  proof (cases n)
    case 0
    then show ?thesis
      by (intro card_ge_0_finite) simp
  next
    case (Suc m)
    then show ?thesis
    proof (cases "F = {}")
      case True
      with Suc show ?thesis
        using not_finite_existsD by auto
    next
      case False
      with Suc assms show ?thesis
        by (intro card_ge_0_finite, subst card_eq) (auto simp: card_gt_0_iff)
    qed
  qed
qed

locale wf_ranking_primal_dual_prob_F_competitive = wf_ranking_primal_dual_F_competitive +
  fixes \<pi> :: "'a list" and M
  defines "M \<equiv> Pi\<^sub>M L (\<lambda>_. uniform_measure lborel {0..1::real})"
  assumes perm: "\<pi> \<in> permutations_of_set R"


  assumes g_funcset: "g \<in> {0..1} \<rightarrow> {0..1}"
  assumes g_mono: "mono_on g {0..1}"
  assumes g_One: "g 1 = 1"
  assumes g_borel: "g \<in> borel_measurable borel"

  assumes F_gt_0: "0 < F"
begin

abbreviation "K_uniform \<equiv> (\<lambda>_. uniform_measure lborel {0..1::real})"

interpretation input_prob_space: prob_space M
  unfolding M_def
  by (intro prob_space_PiM prob_space_uniform_measure) auto

abbreviation "expected_dual \<equiv> vec n (\<lambda>i. input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ i))"

lemma dual_expectation_feasible_component_wise:
  assumes "i \<in> L"
  assumes "j \<in> R"
  assumes "{i,j} \<in> G"

shows "input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ Vs_enum i) + input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ Vs_enum j) \<ge> 1"
  (is "?d \<ge> 1")
proof -
  have "?d = input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ Vs_enum i + (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ Vs_enum j)"
    (is "?d = input_prob_space.expectation ?E")
    apply (intro Bochner_Integration.integral_add[symmetric])
    sorry

  also have "\<dots> = enn2real (integral\<^sup>N (Pi\<^sub>M L K_uniform) ?E)"
    unfolding M_def
    apply (intro integral_eq_nn_integral)
      \<comment> \<open>\<^term>\<open>integrable\<close> not straightforward?, \<^term>\<open>0 \<le> ?E Y\<close> is though\<close>
    sorry

  also from \<open>i \<in> L\<close> have "\<dots> = enn2real (integral\<^sup>N (Pi\<^sub>M (insert i (L - {i})) K_uniform) ?E)"
    by (auto intro: arg_cong[where f = enn2real] arg_cong2[where f = "integral\<^sup>N"] PiM_cong)

  also have "\<dots> = enn2real (integral\<^sup>N (distr (K_uniform i \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) K_uniform) (Pi\<^sub>M (insert i (L - {i})) K_uniform) (\<lambda>(y,Y). Y(i := y))) ?E)"
    by (intro arg_cong[where f = enn2real] arg_cong2[where f = "integral\<^sup>N"] distr_pair_PiM_eq_PiM[symmetric] prob_space_uniform_measure)
       auto

  also have "\<dots> = enn2real (integral\<^sup>N (K_uniform i \<Otimes>\<^sub>M Pi\<^sub>M (L - {i}) K_uniform) (?E \<circ> (\<lambda>(y,Y). Y(i := y))))"
    unfolding comp_def
    apply (intro arg_cong[where f = enn2real] nn_integral_distr)
     apply measurable
    sorry

  also have "\<dots> = enn2real (\<integral>\<^sup>+Y. \<integral>\<^sup>+y. ?E (Y(i := y)) \<partial>K_uniform i \<partial>Pi\<^sub>M (L - {i}) K_uniform)"
    apply (subst pair_sigma_finite.nn_integral_snd[of "K_uniform i" "Pi\<^sub>M (L - {i}) K_uniform" "?E \<circ> (\<lambda>(y,Y). Y(i := y))", symmetric])
    subgoal
      \<comment> \<open>should workout pretty easily\<close>
      sorry
    subgoal
      \<comment> \<open>not sure about this one\<close>
      sorry
    by simp

  also have "\<dots> \<ge> enn2real (\<integral>\<^sup>+Y. \<integral>\<^sup>+y. g y / F * indicator {0..<y\<^sub>c Y G \<pi> i j} y + (1-g(y\<^sub>c Y G \<pi> i j))/F
    \<partial>K_uniform i \<partial>Pi\<^sub>M (L - {i}) K_uniform)" (is "_ \<ge> ?int_yc")
  proof (intro enn2real_mono nn_integral_mono, goal_cases)
    case (1 Y y)
    have "ennreal (g y / F * indicator {0..< y\<^sub>c Y G \<pi> i j} y + (1 - g (y\<^sub>c Y G \<pi> i j)) / F) =
      ennreal (g y / F * indicator {0..< y\<^sub>c Y G \<pi> i j} y) + ennreal ((1 - g (y\<^sub>c Y G \<pi> i j)) / F)"
      apply (intro ennreal_plus)
       apply (auto)
      sorry

    also have "\<dots> \<le> ennreal ((snd \<circ> snd) (ranking_primal_dual (Y(i := y)) \<pi>) $ Vs_enum i) +
      ennreal ((snd \<circ> snd) (ranking_primal_dual (Y(i:= y)) \<pi>) $ Vs_enum j)"
      apply (intro add_mono)
       apply (auto simp: indicator_def)
      subgoal
        \<comment> \<open>apply dominance lemma\<close>
        sorry
      subgoal
        \<comment> \<open>apply monotonicity lemma\<close>
        sorry
      done

    also have "\<dots> = (snd \<circ> snd) (ranking_primal_dual (Y(i := y)) \<pi>) $ Vs_enum i +
      (snd \<circ> snd) (ranking_primal_dual (Y(i:= y)) \<pi>) $ Vs_enum j"
      apply (intro ennreal_plus[symmetric])
      sorry

    finally show ?case .
  next
    case 2
    show ?case
      \<comment> \<open>can bound again with @{thm nn_integral_mono} and (constant) upper bounds on dual solution (in [0..1])\<close>
      apply auto
      sorry
  qed

  finally have d_geq_int_yc: "?d \<ge> ?int_yc" .

  have "?int_yc = enn2real (\<integral>\<^sup>+Y. \<integral>\<^sup>+y. (g y * indicator {0..<y\<^sub>c Y G \<pi> i j} y + (1 - g(y\<^sub>c Y G \<pi> i j))) / ennreal F
    \<partial>K_uniform i \<partial>Pi\<^sub>M (L - {i}) K_uniform)"
    using F_gt_0
    sorry

  also have "\<dots> = enn2real (\<integral>\<^sup>+Y. \<integral>\<^sup>+y. g y * indicator {0..<y\<^sub>c Y G \<pi> i j} y + (1 - g(y\<^sub>c Y G \<pi> i j))
    \<partial>K_uniform i / F \<partial>Pi\<^sub>M (L - {i}) K_uniform)"
    using g_borel
    by (intro arg_cong[where f = enn2real] nn_integral_cong nn_integral_divide, measurable)

  also have "\<dots> = enn2real (\<integral>\<^sup>+Y. \<integral>\<^sup>+y. g y * indicator {0..<y\<^sub>c Y G \<pi> i j} y + (1 - g(y\<^sub>c Y G \<pi> i j))
    \<partial>K_uniform i \<partial>Pi\<^sub>M (L - {i}) K_uniform / F)"
    using g_borel
    apply (intro arg_cong[where f = enn2real] nn_integral_divide, measurable)
    sorry

  also have "\<dots> = enn2real (\<integral>\<^sup>+Y. \<integral>\<^sup>+y. ennreal (g y * indicator {0..<y\<^sub>c Y G \<pi> i j} y) + ennreal (1 - g(y\<^sub>c Y G \<pi> i j))
    \<partial>K_uniform i \<partial>Pi\<^sub>M (L - {i}) K_uniform / F)"
    apply (intro arg_cong[where f = enn2real] arg_cong2[where f = divide] nn_integral_cong ennreal_plus)
      apply auto
    sorry

  also have "\<dots> = enn2real (\<integral>\<^sup>+Y. (\<integral>\<^sup>+y. g y * indicator {0..<y\<^sub>c Y G \<pi> i j} y \<partial>K_uniform i) + (\<integral>\<^sup>+_. 1 - g(y\<^sub>c Y G \<pi> i j) \<partial>K_uniform i)
    \<partial>Pi\<^sub>M (L - {i}) K_uniform / F)"
    using g_borel
    by (intro arg_cong[where f = enn2real] arg_cong2[where f = divide] nn_integral_cong nn_integral_add, measurable)

  also have "\<dots> = enn2real (\<integral>\<^sup>+Y. (\<integral>\<^sup>+y. g y * indicator {0..<y\<^sub>c Y G \<pi> i j} y \<partial>K_uniform i) + (1 - g (y\<^sub>c Y G \<pi> i j))
    \<partial>Pi\<^sub>M (L - {i}) K_uniform / F)"
    by (intro arg_cong[where f = enn2real] arg_cong2[where f = divide] nn_integral_cong arg_cong2[where f = plus])
      auto

  also have "\<dots> \<ge> enn2real (\<integral>\<^sup>+Y. F \<partial>Pi\<^sub>M (L - {i}) K_uniform / F)" (is "_ \<ge> ?int_F")
    apply (intro enn2real_mono divide_right_mono_ennreal nn_integral_mono)
    subgoal for Y
    \<comment> \<open>use assumption on \<^term>\<open>g\<close>\<close>
      sorry
    subgoal
    \<comment> \<open>same as above, bound by constants\<close>
      sorry
    done

  finally have int_yc_geq_int_F: "?int_yc \<ge> ?int_F" .

  interpret prob_space_L_minus_i: prob_space "Pi\<^sub>M (L - {i}) K_uniform"
    by (intro prob_space_PiM prob_space_uniform_measure, auto)

  have "?int_F = enn2real (ennreal F / F)"
    by (intro arg_cong[where f = enn2real] arg_cong2[where f = divide])
       (simp_all add: prob_space_L_minus_i.emeasure_space_1)

  also have "\<dots> = 1"
    using F_gt_0
    by simp

  finally have "?int_F = 1" .

  with d_geq_int_yc int_yc_geq_int_F show ?thesis
    by linarith
qed

lemma G_not_empty_if:
  assumes "i < m"
  shows "G \<noteq> {}"
  using assms
  unfolding m_def
  by fastforce

lemma from_nat_into_G_E_aux:
  assumes "i < m"
  obtains e where "e \<in> G" "from_nat_into G i = e"
  using assms
  by (metis G_not_empty_if from_nat_into)

lemma from_nat_into_G_E:
  assumes "i < m"
  obtains l r where "{l,r} \<in> G" "from_nat_into G i = {l,r}" "l \<in> L" "r \<in> R"
  using assms bipartite
  by (metis bipartite_edgeE from_nat_into_G_E_aux)

lemma Vs_enum_inv_eq_iff:
  assumes "v \<in> Vs G"
  assumes "i < n"
  shows "Vs_enum_inv i = v \<longleftrightarrow> i = Vs_enum v"
  using assms
  by auto

lemma index_set_Int_is_doubleton:
  assumes "l \<in> L" "r \<in> R"
  shows "{0..<n} \<inter> {i. Vs_enum_inv i = l \<or> Vs_enum_inv i = r} = {Vs_enum l, Vs_enum r}"
  using assms
  apply (auto intro: L_enum_less_n R_enum_less_n simp: fin_L to_nat_on_less_card)
      apply (metis Vs_enum_def Vs_enum_inv)
  apply (metis Un_iff Vs_cases Vs_enum_def Vs_enum_inv parts_minimal)
  done


theorem expected_dual_feasible: "(transpose_mat \<circ> map_mat real) incidence_matrix *\<^sub>v expected_dual \<ge> 1\<^sub>v m"
  unfolding less_eq_vec_def
proof (intro conjI allI impI, goal_cases)
  case 1
  then show ?case unfolding incidence_matrix_def
    by auto
next
  case (2 i)
  then have "i < m"
    unfolding incidence_matrix_def
    by auto

  then obtain l r where lr: "{l,r} \<in> G" "from_nat_into G i = {l,r}" "l \<in> L" "r \<in> R"
    by (auto elim: from_nat_into_G_E)

  with bipartite have index_neq: "Vs_enum l \<noteq> Vs_enum r"
    by (intro Vs_enum_neqI) (auto elim: bipartite_edgeE)

  from \<open>i < m\<close> have "1\<^sub>v m $ i = 1"
    by simp

  also from lr have "\<dots> \<le> input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ Vs_enum l) + 
    input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ Vs_enum r)"
    by (intro dual_expectation_feasible_component_wise)

  also from index_neq have "\<dots> = (\<Sum>j\<in>{Vs_enum l, Vs_enum r}. input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual Y \<pi>) $ j))"
    by simp

  also from \<open>{l,r} \<in> G\<close> \<open>i < m\<close> have "\<dots> = ((transpose_mat \<circ> map_mat real) incidence_matrix *\<^sub>v vec n (\<lambda>i. input_prob_space.expectation (\<lambda>Y. (snd \<circ> snd) (ranking_primal_dual' Y ({}, 0\<^sub>v m, 0\<^sub>v n) \<pi>) $ i))) $ i"
    unfolding incidence_matrix_def
    apply (auto simp: mult_mat_vec_def scalar_prod_def sum.cong[OF index_set_Int_is_doubleton] elim!: from_nat_into_G_E)
    by (metis Vs_cases Vs_enum_def doubleton_eq_iff edges_are_Vs(2) lr(2))

  finally show ?case .
qed

end


end