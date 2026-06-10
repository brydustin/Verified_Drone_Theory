theory Scratch_b5
  imports "Applied_Math_Appendix.Nonemptiness_Robust"
begin

lemma sum_reindex_embed:
  fixes \<iota> :: "6 \<Rightarrow> 'm::finite" and g :: "'m \<Rightarrow> 'a::comm_monoid_add"
  assumes inj: "inj \<iota>" and van: "\<And>n. n \<notin> range \<iota> \<Longrightarrow> g n = 0"
  shows "(\<Sum>n\<in>UNIV. g n) = (\<Sum>k\<in>UNIV. g (\<iota> k))"
proof -
  have "(\<Sum>n\<in>(UNIV::'m set). g n) = (\<Sum>n\<in>range \<iota>. g n)"
    by (rule sum.mono_neutral_right[OF finite_class.finite_UNIV subset_UNIV]) (simp add: van)
  also have "(\<Sum>n\<in>range \<iota>. g n) = (\<Sum>k\<in>(UNIV::6 set). (g \<circ> \<iota>) k)"
    by (rule sum.reindex[OF inj])
  also have "(\<Sum>k\<in>(UNIV::6 set). (g \<circ> \<iota>) k) = (\<Sum>k\<in>(UNIV::6 set). g (\<iota> k))"
    by (simp only: o_def)
  finally show ?thesis .
qed

lemma DM_paper_x_regular_point_c0_gen:
  assumes c6: "6 \<le> CARD('n)"
  shows "\<exists>y0::(real^2)^'n. surj (DM_paper_x y0 c0_paper)"
proof -
  obtain x0 :: "(real^2)^6" where reg6: "surj (DM_paper_x x0 c0_paper)"
    using DM_paper_x_regular_point_c0 by blast
  have c: "card (UNIV::6 set) \<le> card (UNIV::'n set)" using c6 by simp
  obtain \<iota> :: "6 \<Rightarrow> 'n" where inj\<iota>: "inj \<iota>"
    using card_le_inj[OF finite_class.finite_UNIV finite_class.finite_UNIV c] by (auto simp: inj_def)
  define xf :: "6 \<Rightarrow> real^2" where "xf = vec_nth x0"
  define y0 :: "(real^2)^'n" where "y0 = vec_lambda (\<lambda>n. if n \<in> range \<iota> then xf (inv_into (UNIV::6 set) \<iota> n) else (0::real^2))"
  have y0v: "\<And>k. y0 $ (\<iota> k) = x0 $ k" by (simp add: y0_def xf_def inv_f_f[OF inj\<iota>])
  have y0z: "\<And>n. n \<notin> range \<iota> \<Longrightarrow> y0 $ n = 0" by (simp add: y0_def)
  have "surj (DM_paper_x y0 c0_paper)"
    unfolding surj_def
  proof (rule allI)
    fix z :: "complex^6"
    obtain h0 :: "(real^2)^6" where h0: "z = DM_paper_x x0 c0_paper h0"
      using reg6 by (auto simp: surj_def)
    define hf :: "6 \<Rightarrow> real^2" where "hf = vec_nth h0"
    define h :: "(real^2)^'n" where "h = vec_lambda (\<lambda>n. if n \<in> range \<iota> then hf (inv_into (UNIV::6 set) \<iota> n) else (0::real^2))"
    have hv: "\<And>k. h $ (\<iota> k) = h0 $ k" by (simp add: h_def hf_def inv_f_f[OF inj\<iota>])
    have hz: "\<And>n. n \<notin> range \<iota> \<Longrightarrow> h $ n = 0" by (simp add: h_def)
    have cA: "d_A_moment_x y0 c0_paper h = d_A_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). d_phase c0_paper y0 h n) = (\<Sum>k\<in>(UNIV::6 set). d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_A_moment_x_def)
    qed
    have cM1: "d_M1_moment_x y0 c0_paper h = d_M1_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real ((h$n)$1) * phase c0_paper y0 n + of_real ((y0$n)$1) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real ((h$(\<iota> k))$1) * phase c0_paper y0 (\<iota> k) + of_real ((y0$(\<iota> k))$1) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real ((h0$k)$1) * phase c0_paper x0 k + of_real ((x0$k)$1) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M1_moment_x_def)
    qed
    have cM2: "d_M2_moment_x y0 c0_paper h = d_M2_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real ((h$n)$2) * phase c0_paper y0 n + of_real ((y0$n)$2) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real ((h$(\<iota> k))$2) * phase c0_paper y0 (\<iota> k) + of_real ((y0$(\<iota> k))$2) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real ((h0$k)$2) * phase c0_paper x0 k + of_real ((x0$k)$2) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M2_moment_x_def)
    qed
    have cM11: "d_M11_moment_x y0 c0_paper h = d_M11_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real (2 * ((y0$n)$1) * ((h$n)$1)) * phase c0_paper y0 n + of_real (((y0$n)$1)\<^sup>2) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((y0$(\<iota> k))$1) * ((h$(\<iota> k))$1)) * phase c0_paper y0 (\<iota> k) + of_real (((y0$(\<iota> k))$1)\<^sup>2) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((x0$k)$1) * ((h0$k)$1)) * phase c0_paper x0 k + of_real (((x0$k)$1)\<^sup>2) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M11_moment_x_def)
    qed
    have cM12: "d_M12_moment_x y0 c0_paper h = d_M12_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real (dw_M12 (y0$n) (h$n)) * phase c0_paper y0 n + of_real (w_M12 (y0$n)) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real (dw_M12 (y0$(\<iota> k)) (h$(\<iota> k))) * phase c0_paper y0 (\<iota> k) + of_real (w_M12 (y0$(\<iota> k))) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def dw_M12_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real (dw_M12 (x0$k) (h0$k)) * phase c0_paper x0 k + of_real (w_M12 (x0$k)) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M12_moment_x_def)
    qed
    have cM22: "d_M22_moment_x y0 c0_paper h = d_M22_moment_x x0 c0_paper h0"
    proof -
      have "(\<Sum>n\<in>(UNIV::'n set). of_real (2 * ((y0$n)$2) * ((h$n)$2)) * phase c0_paper y0 n + of_real (((y0$n)$2)\<^sup>2) * d_phase c0_paper y0 h n)
          = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((y0$(\<iota> k))$2) * ((h$(\<iota> k))$2)) * phase c0_paper y0 (\<iota> k) + of_real (((y0$(\<iota> k))$2)\<^sup>2) * d_phase c0_paper y0 h (\<iota> k))"
        by (rule sum_reindex_embed[OF inj\<iota>]) (simp add: d_phase_def hz)
      also have "\<dots> = (\<Sum>k\<in>(UNIV::6 set). of_real (2 * ((x0$k)$2) * ((h0$k)$2)) * phase c0_paper x0 k + of_real (((x0$k)$2)\<^sup>2) * d_phase c0_paper x0 h0 k)"
        by (rule sum.cong[OF refl]) (simp add: phase_def d_phase_def y0v hv)
      finally show ?thesis by (simp add: d_M22_moment_x_def)
    qed
    have key: "DM_paper_x y0 c0_paper h = DM_paper_x x0 c0_paper h0"
      unfolding Finite_Cartesian_Product.vec_eq_iff
    proof (intro allI)
      fix k :: 6
      show "DM_paper_x y0 c0_paper h $ k = DM_paper_x x0 c0_paper h0 $ k"
        using exhaust_6[of k]
        by (simp add: DM_paper_x_eq_MM Moment_Map.DM_paper_x_def cA cM1 cM11 cM12 cM2 cM22)
    qed
    show "\<exists>h'. z = DM_paper_x y0 c0_paper h'" using key h0 by metis
  qed
  thus ?thesis by blast
qed

end
