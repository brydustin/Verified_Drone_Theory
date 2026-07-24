theory Scratch_D3ResidualSplit
  imports "Applied_Math_M5_ActualD3Argument.Scratch_ActualD3Argument"
begin

section \<open>The Xi-zero residual, split at the fold order\<close>

text \<open>
  The actual-D3 argument reduces the whole design-point D3 wing to three
  residuals \<open>meager (fst ` D3ActualXiZeroNonphaseIncidence V y)\<close>,
  \<open>y \<in> {-\<pi>, 0, \<pi>}\<close> (see \<open>Scratch_ActualD3Argument\<close>,
  \<open>robust4_horizontal_actual_interior_projection_decomp\<close> at l.1524 and
  \<open>m5_D34_D3_collinear_robust4_of_actual_Xi_zero_residuals\<close> at l.1919).

  Each residual is a degenerate fold: on it \<open>gradU = 0\<close>, \<open>detHess = 0\<close>,
  nonphase, and \<open>Xi = 0 \<longleftrightarrow> h11 = 0\<close>
  (\<open>robust4_horizontal_arc_actual_Xi_horizontal_value\<close>, l.639), which with
  \<open>detHess = 0\<close> forces \<open>HessU = diag(0, h22)\<close>, hence
  \<open>trans := (HessU \<cdot> (1,0))\<^sub>1 = h11 = 0\<close>.  The trans-based critical-\<open>t\<close>
  graph engine \<open>arc_schur_point_open_actual_patch\<close> (used by the already-proven
  \<open>Xi \<noteq> 0\<close> sibling via \<open>robust4_horizontal_actual_nonphase_point_open_patch\<close>,
  l.1304) therefore cannot fire here.

  The correct route uses the live transverse direction along the arc, namely
  \<open>\<partial>\<^sub>t h11 = h11'\<close> (already computed as the cubic-map \<open>t\<close>-derivative second
  component, \<open>tcomponent2\<close>, ll.2609--2620), noting that the perpendicular
  \<open>gradU\<^sub>2\<close> cut survives a \<open>t = \<tau>(x)\<close> substitution because
  \<open>\<partial>\<^sub>t gradU\<^sub>2 = h12 = 0\<close>
  (\<open>robust4_actual_Xi_zero_incidence_gradU2_arc_derivative_zero\<close>, l.2054).
  This splits the residual by the fold order:

    \<^item> simple fold  \<open>h11' \<noteq> 0\<close>: an IFT graph for \<open>h11 = 0\<close> pins \<open>t = \<tau>(x)\<close>,
      after which the residual lies in a codimension-1 nowhere-dense set in
      \<open>x\<close> (live \<open>\<partial>\<^sub>x gradU\<^sub>2\<close>), Lindel\"of-patched to a meager set --- structurally
      the existing \<open>nonphase\<close> pipeline with the graph equation
      \<open>gradU\<^sub>1 = 0\<close> replaced by \<open>h11 = 0\<close>;

    \<^item> flat fold  \<open>h11' = 0\<close>: the higher-order fold, to be settled by the next
      \<open>t\<close>-derivative (third-derivative ingredients in \<open>Scratch_D3Hess\<close>) or shown
      negligible.

  This leaf records the split itself as a strict theorem: the residual is
  meager as soon as both fold branches are meager.  It is the honest
  explicit-hypothesis pattern already used for the D3 capstone input
  (\<open>Scratch_D3ArcCount\<close>), pinning the two remaining sub-goals in exactly the
  form the \<open>h11'\<close>-IFT construction produces them.
\<close>

text \<open>
  The arc-derivative of the \<open>(1,1)\<close> Hessian entry \<open>h11\<close> at the incidence
  angle \<open>snd q\<close>, along the horizontal arc \<open>t \<mapsto> (t, y)\<close> at the design point.
  Its non-vanishing is the simple-fold condition.
\<close>

definition d3_residual_h11_arc_deriv ::
    "(((real^2)^'n::finite) \<times> real) \<Rightarrow> real \<Rightarrow> real"
  where
  "d3_residual_h11_arc_deriv q y =
     deriv (\<lambda>t. vec_nth
        (vec_nth
          (HessU (cvec_dip (vector [pi / 2, 0]) (vector [0, 0]))
             gain_dip (fst q) (vector [t, y])) 1) 1)
       (snd q)"

theorem residual_meager_of_fold_branches:
  fixes V :: "((real^2)^'n::finite) set" and y :: real
  assumes simple:
      "meager (fst ` {q \<in> D3ActualXiZeroNonphaseIncidence V y.
                        d3_residual_h11_arc_deriv q y \<noteq> 0})"
    and flat:
      "meager (fst ` {q \<in> D3ActualXiZeroNonphaseIncidence V y.
                        d3_residual_h11_arc_deriv q y = 0})"
  shows "meager (fst ` D3ActualXiZeroNonphaseIncidence V y)"
proof -
  let ?R = "D3ActualXiZeroNonphaseIncidence V y"
  let ?A = "{q \<in> ?R. d3_residual_h11_arc_deriv q y \<noteq> 0}"
  let ?B = "{q \<in> ?R. d3_residual_h11_arc_deriv q y = 0}"
  have RAB: "?R = ?A \<union> ?B" by auto
  have "fst ` ?R = fst ` ?A \<union> fst ` ?B"
    by (subst RAB) (simp add: image_Un)
  moreover have "meager (fst ` ?A \<union> fst ` ?B)"
    by (rule meager_Un[OF simple flat])
  ultimately show ?thesis by simp
qed

end
