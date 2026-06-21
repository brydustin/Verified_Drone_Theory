theory Saddle_Cover
  imports "Applied_Math_Morse.Hadamard_2D" "Applied_Math_Morse.Morse_Saddle_2D"
begin

theorem smooth3_saddle_cover:
  fixes f :: "real^2 \<Rightarrow> real" and G H1 H2 K11 K12 K22 :: "real^2 \<Rightarrow> real^2" and p :: "real^2" and \<rho>0 :: real
  assumes \<rho>0: "\<rho>0 > 0"
    and sm: "SMOOTH3 f G H1 H2 K11 K12 K22 (ball p \<rho>0)"
    and fp: "f p = 0"
    and flat: "G p = 0"
    and indef: "((H1 p)$2)\<^sup>2 - (H1 p)$1 * (H2 p)$2 > 0"
  obtains \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real where
      "0 < r" "a1 \<le> b1" "a2 \<le> b2" "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
      "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
      "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
proof -
  \<comment> \<open>STEP 1: flatness as a derivative.  From SMOOTH3, f has the gradient derivative at p; flat = G p = 0
      turns it into the zero functional.\<close>
  have pin0: "p \<in> ball p \<rho>0" using \<rho>0 by simp
  have Gder_p: "(f has_derivative (\<lambda>h. inner (G p) h)) (at p)"
    using sm pin0 unfolding SMOOTH3_def by blast
  have Dfp: "(f has_derivative (\<lambda>_. 0)) (at p)"
  proof -
    have "(\<lambda>h::real^2. inner (G p) h) = (\<lambda>_. 0)"
      by (rule ext) (simp add: flat)
    thus ?thesis using Gder_p by simp
  qed

  \<comment> \<open>STEP 2: apply hadamard2 (structured obtains-consumption) to land the quadratic form.\<close>
  show ?thesis
  proof (rule hadamard2[OF \<rho>0 sm fp Dfp])
    fix a b c :: "real^2 \<Rightarrow> real" and ga gb gc :: "real^2 \<Rightarrow> real^2" and \<rho> :: real
    assume \<rho>pos: "0 < \<rho>" and \<rho>le: "\<rho> \<le> \<rho>0"
      and aC1H: "Hadamard_2D.C1field a ga (ball p \<rho>)"
      and bC1H: "Hadamard_2D.C1field b gb (ball p \<rho>)"
      and cC1H: "Hadamard_2D.C1field c gc (ball p \<rho>)"
      and form: "\<And>x. x \<in> ball p \<rho> \<Longrightarrow>
          f x = a x * ((x-p)$1)\<^sup>2 + 2 * b x * ((x-p)$1) * ((x-p)$2) + c x * ((x-p)$2)\<^sup>2"
      and ap: "2 * a p = (H1 p)$1" and bp: "2 * b p = (H1 p)$2" and cp: "2 * c p = (H2 p)$2"

    \<comment> \<open>BRIDGE: the two theories define \<open>C1field\<close> independently (Morse_Saddle does not import
        Hadamard), so convert the Hadamard-side C1 fields to the Morse-side ones used by the
        saddle theorems.  The two definitions are textually identical.\<close>
    have aC1: "Morse_Saddle_2D.C1field a ga (ball p \<rho>)"
      using aC1H unfolding Hadamard_2D.C1field_def Morse_Saddle_2D.C1field_def .
    have bC1: "Morse_Saddle_2D.C1field b gb (ball p \<rho>)"
      using bC1H unfolding Hadamard_2D.C1field_def Morse_Saddle_2D.C1field_def .
    have cC1: "Morse_Saddle_2D.C1field c gc (ball p \<rho>)"
      using cC1H unfolding Hadamard_2D.C1field_def Morse_Saddle_2D.C1field_def .

    \<comment> \<open>STEP 3: the discriminant on a,b,c is positive (it is 1/4 of the Hessian discriminant).\<close>
    have disc: "(b p)\<^sup>2 - a p * c p > 0"
    proof -
      have e1: "(H1 p)$1 = 2 * a p" using ap by simp
      have e2: "(H1 p)$2 = 2 * b p" using bp by simp
      have e3: "(H2 p)$2 = 2 * c p" using cp by simp
      have "0 < ((H1 p)$2)\<^sup>2 - (H1 p)$1 * (H2 p)$2" using indef by simp
      also have "((H1 p)$2)\<^sup>2 - (H1 p)$1 * (H2 p)$2
               = 4 * ((b p)\<^sup>2 - a p * c p)"
        by (simp add: e1 e2 e3 power2_eq_square algebra_simps)
      finally show ?thesis by simp
    qed

    \<comment> \<open>STEP 4: case split on which leading coefficient is nonzero.\<close>
    show thesis
    proof (cases "a p \<noteq> 0")
      case True
      show thesis
      proof (rule saddle_form_two_arcs[OF \<rho>pos aC1 bC1 cC1 True disc form])
        fix \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real
        assume "0 < r" "a1 \<le> b1" "a2 \<le> b2"
          "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
          "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
          "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
        thus thesis by (rule that)
      qed
    next
      case False
      then have apz: "a p = 0" by simp
      show thesis
      proof (cases "c p \<noteq> 0")
        case True
        show thesis
        proof (rule saddle_form_two_arcs_cform[OF \<rho>pos aC1 bC1 cC1 True disc form])
          fix \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real
          assume "0 < r" "a1 \<le> b1" "a2 \<le> b2"
            "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
            "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
            "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
          thus thesis by (rule that)
        qed
      next
        case False
        then have cpz: "c p = 0" by simp
        have bpz: "b p \<noteq> 0"
        proof -
          have "(b p)\<^sup>2 > 0" using disc apz cpz by simp
          thus ?thesis by (auto simp: power2_eq_square)
        qed
        show thesis
        proof (rule saddle_form_two_arcs_purecross[OF \<rho>pos aC1 bC1 cC1 apz cpz bpz form])
          fix \<gamma>1 \<gamma>2 :: "real \<Rightarrow> real^2" and a1 b1 a2 b2 r :: real
          assume "0 < r" "a1 \<le> b1" "a2 \<le> b2"
            "\<gamma>1 C1_differentiable_on {a1..b1}" "\<gamma>2 C1_differentiable_on {a2..b2}"
            "p \<in> \<gamma>1 ` {a1..b1}" "p \<in> \<gamma>2 ` {a2..b2}"
            "{x. f x = 0} \<inter> ball p r \<subseteq> \<gamma>1 ` {a1..b1} \<union> \<gamma>2 ` {a2..b2}"
          thus thesis by (rule that)
        qed
      qed
    qed
  qed
qed

end
