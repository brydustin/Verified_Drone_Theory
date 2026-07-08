theory Scratch_rank3
  imports "Applied_Math_D34_Analytic.D34_Analytic_Bridge"
begin

text \<open>CONSOLIDATED (2026-07-08).  The rank-3 criterion (cor:vpair11) --- verified
  here and spliced verbatim into \<open>D34_Analytic_Bridge.thy\<close>, in two pieces:

  PART 1 (the invariant fix for the \<open>\<Phi>\<^sub>1\<close>-independence hypothesis):
  \<^enum> the paper's block-triangular argument needs \<open>\<Phi>\<^sub>1\<close> INDEPENDENT of every v-slot,
    a fact of their SPECIFIC omega-parametrization, NOT automatic for our
    \<open>(sin\<theta>cos\<phi>,\<dots>)\<close> angular coordinates (\<open>gradU_dip_xderiv_perp_slot\<close> gives BOTH
    components \<open>j=1,2\<close> the SAME nonzero shape \<open>2g\<^sub>0(\<gamma>\<^sub>j\<bullet>v)W_m\<close> --- caught and
    resolved, not glossed over);
  \<^enum> \<open>e_par\<close> (the omega direction pushing forward to \<open>c\<close> under \<open>Dcvec_dip\<close>, via
    \<open>bij_matrix_vector_mult\<close> + \<open>inv_into UNIV\<close> --- GOTCHA: bare \<open>inv\<close> is algebra
    structure syntax in the merged heap) and \<open>Dcvec_dip_e_par\<close> (its defining
    property, proven via ELEMENTARY \<open>matrix_def\<close>/basis-decomposition rather than
    \<open>matrix_works\<close>/\<open>matrix_vector_mul\<close> --- GOTCHA: those library lemmas resolve to
    the \<open>Vector_Spaces.linear (*s) (*s)\<close> typeclass variant in this heap, NOT the
    standard \<open>linear\<close> from \<open>bounded_linear.linear\<close>, and no bridging fact was
    findable --- the elementary route sidesteps this entirely);
  \<^enum> \<open>Phi_par := gradU \<bullet> e_par\<close> (playing \<open>\<Phi>\<^sub>1\<close>'s role) and
    \<open>Phi_par_perp_slot_zero\<close>: its perpendicular-slot \<open>x\<close>-derivative vanishes BY
    CONSTRUCTION (\<open>D\<Phi>_par(slot m v) = 2g\<^sub>0 W_m (Dcvec_dip(e_par)\<bullet>v) = 2g\<^sub>0 W_m
    (c\<bullet>v) = 0\<close>) --- the invariant analogue of the paper's own omega-gauge choice.

  PART 2 (the criterion itself):
  \<^enum> \<open>Jac3\<close>: the 3x3 Jacobian determinant of \<open>(\<Phi>_par,\<Phi>2,G11)\<close> restricted to
    directions \<open>(U, slot_i(perp2 c), slot_j(perp2 c))\<close>, via the existing \<open>det3\<close>
    primitive;
  \<^enum> \<^bold>\<open>Jac3_identity\<close>: \<open>Jac3 = D\<Phi>_par(U) * Delta_ij(i,j)\<close> --- the block-triangular
    cofactor-expansion collapse, using \<open>Phi_par_perp_slot_zero\<close> to zero the
    (1,2)/(1,3) entries;
  \<^enum> \<^bold>\<open>Jac3_nonzero_criterion\<close>: given the paper's own two hypotheses ---
    \<open>D\<Phi>_par(U)\<noteq>0\<close> for some x-direction U (their \<open>U\<in>E_u, D\<Phi>_1(U)\<noteq>0\<close>) and
    \<open>Delta_ij(i,j)\<noteq>0\<close> --- \<open>Jac3 \<noteq> 0\<close>, i.e. the restriction of
    \<open>D(\<Phi>_par,\<Phi>2,G11)\<close> to \<open>(U,slot_i,slot_j)\<close> has full rank 3.  This IS
    \<open>cor:vpair11\<close>, in fully invariant (gauge-free) form.

  GOTCHA: another \<open>vec_eq_iff\<close>-as-simp-member failure (twice, in Part 1) --- plain
  \<open>simp add: vec_eq_iff ...\<close> does NOT auto-apply the iff as a splitting rule here;
  use the structured \<open>proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2],
  intro allI) fix i :: 2 show ...\<close> pattern instead.  GOTCHA (Part 2): the \<open>U\<close>
  fixes-clause was mistyped as \<open>real^2\<close> instead of \<open>(real^2)^'n\<close> (U is an x-space
  tangent DIRECTION, matching \<open>x\<close>'s type, not an omega-space vector like
  \<open>\<omega>,\<omega>0,\<omega>s\<close>) --- caught immediately via the resulting type-clash error.
  Checks below guard the interface.\<close>

thm e_par_def Dcvec_dip_e_par
thm Phi_par_def has_derivative_gradU_inner_x
thm Phi_par_perp_slot_zero
thm Jac3_def Jac3_identity
thm Jac3_nonzero_criterion

end
