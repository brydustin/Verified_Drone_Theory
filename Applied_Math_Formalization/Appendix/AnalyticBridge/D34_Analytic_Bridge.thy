theory D34_Analytic_Bridge
  imports
    "Applied_Math_Appendix.Nonemptiness_Robust2"
    "Applied_Math_Analytic_Complex.Real_Analytic_IFT"
begin

section \<open>The dipole-specific analytic bridge (the D34 platform)\<close>

text \<open>This theory merges the robust nonemptiness development (through
  \<open>Nonemptiness_Robust2\<close>) with the real-analytic stack (through the analytic
  implicit-function theorem @{thm real_analytic_implicit_function} and the
  multivariate nowhere-dense-zeros workhorse @{thm real_analytic_nowhere_dense_zeros}).
  Its purpose is to discharge the two remaining D3/D4 chart-branch cores of
  \<open>F0_dip_nonempty\<close> by the analytic route:

  \<^enum> every dipole field in sight (\<open>kx\<close>, \<open>ky\<close>, \<open>kz\<close>, \<open>gdip\<close>, \<open>gain_dip\<close>, \<open>cvec_dip\<close>,
    the moment phases, hence \<open>gradU\<close> and \<open>mstarg\<close>) is a polynomial in
    \<open>sin\<close>/\<open>cos\<close>/\<open>gsinc\<close> of affine and bilinear arguments, hence REAL-ANALYTIC
    (this theory, layer 1);
  \<^enum> at a critical point with \<open>det HessU \<noteq> 0\<close> the analytic IFT yields a
    real-analytic critical graph \<open>\<omega> = \<omega>\<^sup>*(x)\<close>, so the local bad set is the zero
    set of the real-analytic function \<open>h x = mstarg (cvec_dip \<omega>0 \<omega>s (\<omega>\<^sup>* x)) x\<close>
    (layer 2);
  \<^enum> by @{thm real_analytic_nowhere_dense_zeros}, \<open>{h = 0}\<close> is closed-in-domain and
    nowhere dense UNLESS \<open>h \<equiv> 0\<close> on a component of the chart domain --- the
    residual transversality witness, the only genuine new mathematics (layer 3).

  This first instalment provides layer 1 for the \<open>\<omega>\<close>-side fields.\<close>

subsection \<open>\<open>gsinc\<close> is the \<open>rsinc\<close> kernel\<close>

lemma gsinc_eq_rsinc: "gsinc = rsinc"
  by (rule ext) (simp add: gsinc_def rsinc_def)

lemma real_analytic_on_gsinc: "real_analytic_on gsinc UNIV"
  by (simp add: gsinc_eq_rsinc real_analytic_on_rsinc)

lemma real_analytic_on_gsinc_comp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>x. gsinc (f x)) U"
  by (simp add: gsinc_eq_rsinc real_analytic_on_rsinc_comp[OF f])

subsection \<open>Vector coordinates are analytic\<close>

lemma real_analytic_on_vec_nth:
  fixes i :: "'i::finite"
  shows "real_analytic_on (\<lambda>\<omega>::real^'i. \<omega> $ i) UNIV"
  by (rule real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_vec_nth])

subsection \<open>The wavevector components and the dipole gain\<close>

lemma real_analytic_on_kx: "real_analytic_on kx UNIV"
  unfolding kx_def[abs_def]
  by (intro real_analytic_on_mult real_analytic_on_sin_comp real_analytic_on_cos_comp
            real_analytic_on_vec_nth)

lemma real_analytic_on_ky: "real_analytic_on ky UNIV"
  unfolding ky_def[abs_def]
  by (intro real_analytic_on_mult real_analytic_on_sin_comp real_analytic_on_vec_nth)

lemma real_analytic_on_kz: "real_analytic_on kz UNIV"
  unfolding kz_def[abs_def]
  by (intro real_analytic_on_cos_comp real_analytic_on_vec_nth)

lemma real_analytic_on_gdip: "real_analytic_on gdip UNIV"
proof -
  have id1: "real_analytic_on (\<lambda>\<theta>::real. \<theta>) UNIV"
    by (rule real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_ident])
  have arg1: "real_analytic_on (\<lambda>\<theta>::real. (pi/2) * (1 - cos \<theta>)) UNIV"
    by (intro real_analytic_on_mult real_analytic_on_diff real_analytic_on_const
              real_analytic_on_cos_comp id1 open_UNIV)
  have arg2: "real_analytic_on (\<lambda>\<theta>::real. (pi/2) * (1 + cos \<theta>)) UNIV"
    by (intro real_analytic_on_mult real_analytic_on_add real_analytic_on_const
              real_analytic_on_cos_comp id1 open_UNIV)
  show ?thesis
    unfolding gdip_def[abs_def]
    by (intro real_analytic_on_mult real_analytic_on_const
              real_analytic_on_gsinc_comp[OF arg1] real_analytic_on_gsinc_comp[OF arg2]
              open_UNIV)
qed

lemma real_analytic_on_gain_dip: "real_analytic_on gain_dip UNIV"
proof -
  have "real_analytic_on (\<lambda>\<omega>::real^2. gdip (\<omega> $ 1)) UNIV"
    by (rule real_analytic_on_compose[OF real_analytic_on_vec_nth
              real_analytic_on_gdip subset_UNIV])
  thus ?thesis
    by (simp add: gain_dip_def[abs_def])
qed

subsection \<open>The steered wavevector \<open>cvec_dip\<close> is analytic\<close>

lemma real_analytic_on_cvec_dip:
  "real_analytic_on (cvec_dip \<omega>0 \<omega>s) UNIV"
proof -
  have c1: "real_analytic_on (\<lambda>\<omega>. (kx \<omega> - kx \<omega>s)
              + ((kx \<omega>0 - kx \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) UNIV"
    by (intro real_analytic_on_add real_analytic_on_diff real_analytic_on_mult
              real_analytic_on_const real_analytic_on_kx real_analytic_on_kz open_UNIV)
  have c2: "real_analytic_on (\<lambda>\<omega>. (ky \<omega> - ky \<omega>s)
              + ((ky \<omega>0 - ky \<omega>s)/(kz \<omega>s - kz \<omega>0)) * (kz \<omega> - kz \<omega>s)) UNIV"
    by (intro real_analytic_on_add real_analytic_on_diff real_analytic_on_mult
              real_analytic_on_const real_analytic_on_ky real_analytic_on_kz open_UNIV)
  show ?thesis
    unfolding cvec_dip_def[abs_def]
    by (intro real_analytic_on_add real_analytic_on_scaleR_vec c1 c2)
qed


section \<open>Layer 2: joint \<open>(c,x)\<close>-analyticity of the moments and \<open>mstarg\<close>\<close>

text \<open>The six paper moments, the six \<open>x\<close>-derivative entries of the moment map, and
  the Gram determinant \<open>mstarg\<close> are REAL-ANALYTIC jointly in \<open>(c, x)\<close>.  Structure:
  \<^enum> a generic closure kit (joint inner products, \<open>Re\<close>/\<open>Im\<close>, complex assembly and
    multiplication, \<open>of_real\<close>, \<open>cis\<close>, \<open>scaleR\<close> into \<open>\<complex>\<close>, determinants of analytic
    matrix fields, and the Gram-matrix entry expansion over a basis);
  \<^enum> the dipole layer: \<open>phase\<close>/\<open>d_phase\<close>, the six moments, the six derivative
    entries, the \<open>transC\<close>-transported entries, and finally \<open>mstarg\<close> itself,
    with the fixed-\<open>c\<close> slice and the \<open>cvec_dip\<close> composition as corollaries.\<close>

subsection \<open>Generic closure kit\<close>

lemma real_analytic_on_inner:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes U: "open U" and F: "real_analytic_on f U" and G: "real_analytic_on g U"
  shows "real_analytic_on (\<lambda>p. f p \<bullet> g p) U"
proof -
  have eq: "(\<lambda>p. f p \<bullet> g p) = (\<lambda>p. \<Sum>b\<in>(Basis::'b set). (f p \<bullet> b) * (g p \<bullet> b))"
    by (rule ext) (rule euclidean_inner)
  have "real_analytic_on (\<lambda>p. \<Sum>b\<in>(Basis::'b set). (f p \<bullet> b) * (g p \<bullet> b)) U"
    by (intro real_analytic_on_sum[OF U finite_Basis] real_analytic_on_mult
              real_analytic_on_inner_component F G)
  thus ?thesis by (simp only: eq)
qed

lemma real_analytic_on_uminus:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. - f p) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  have "real_analytic_on (\<lambda>p. (0::'b) - f p) U"
    by (intro real_analytic_on_diff real_analytic_on_const[OF U] F)
  thus ?thesis by simp
qed

lemma real_analytic_on_Re:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. Re (f p)) U"
proof -
  have "real_analytic_on (\<lambda>p. f p \<bullet> 1) U"
    by (rule real_analytic_on_inner_component[OF F])
  thus ?thesis by (simp add: inner_complex_def)
qed

lemma real_analytic_on_Im:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. Im (f p)) U"
proof -
  have "real_analytic_on (\<lambda>p. f p \<bullet> \<i>) U"
    by (rule real_analytic_on_inner_component[OF F])
  thus ?thesis by (simp add: inner_complex_def)
qed

lemma real_analytic_on_Complex:
  fixes fr fi :: "'a::euclidean_space \<Rightarrow> real"
  assumes U: "open U" and R: "real_analytic_on fr U" and I: "real_analytic_on fi U"
  shows "real_analytic_on (\<lambda>p. Complex (fr p) (fi p)) U"
proof (rule real_analytic_on_componentwise[OF U])
  fix b :: complex assume "b \<in> Basis"
  hence "b = 1 \<or> b = \<i>" by (auto simp: Basis_complex_def)
  thus "real_analytic_on (\<lambda>p. Complex (fr p) (fi p) \<bullet> b) U"
  proof
    assume b: "b = 1"
    have "(\<lambda>p. Complex (fr p) (fi p) \<bullet> b) = fr"
      by (rule ext) (simp add: b inner_complex_def)
    thus ?thesis using R by simp
  next
    assume b: "b = \<i>"
    have "(\<lambda>p. Complex (fr p) (fi p) \<bullet> b) = fi"
      by (rule ext) (simp add: b inner_complex_def)
    thus ?thesis using I by simp
  qed
qed

lemma real_analytic_on_cmult:
  fixes f g :: "'a::euclidean_space \<Rightarrow> complex"
  assumes U: "open U" and F: "real_analytic_on f U" and G: "real_analytic_on g U"
  shows "real_analytic_on (\<lambda>p. f p * g p) U"
proof -
  have eq: "(\<lambda>p. f p * g p)
      = (\<lambda>p. Complex (Re (f p) * Re (g p) - Im (f p) * Im (g p))
                     (Re (f p) * Im (g p) + Im (f p) * Re (g p)))"
    by (rule ext) (simp add: complex_eq_iff)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_Complex[OF U] real_analytic_on_diff real_analytic_on_add
              real_analytic_on_mult real_analytic_on_Re real_analytic_on_Im F G)
qed

lemma real_analytic_on_of_real:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. complex_of_real (f p)) U"
  by (rule real_analytic_on_compose[OF F
        real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_of_real] subset_UNIV])

lemma real_analytic_on_cis:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. cis (f p)) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  have eq: "(\<lambda>p. cis (f p)) = (\<lambda>p. Complex (cos (f p)) (sin (f p)))"
    by (rule ext) (simp add: complex_eq_iff)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_Complex[OF U] real_analytic_on_cos_comp
              real_analytic_on_sin_comp F)
qed

lemma real_analytic_on_scaleR_complex:
  fixes f :: "'a::euclidean_space \<Rightarrow> real" and g :: "'a \<Rightarrow> complex"
  assumes U: "open U" and F: "real_analytic_on f U" and G: "real_analytic_on g U"
  shows "real_analytic_on (\<lambda>p. f p *\<^sub>R g p) U"
proof -
  have eq: "(\<lambda>p. f p *\<^sub>R g p) = (\<lambda>p. complex_of_real (f p) * g p)"
    by (rule ext) (simp add: scaleR_conv_of_real)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_cmult[OF U] real_analytic_on_of_real F G)
qed

lemma real_analytic_on_det:
  fixes M :: "'a::euclidean_space \<Rightarrow> real^'k^'k::finite"
  assumes U: "open U"
    and E: "\<And>i j. real_analytic_on (\<lambda>p. vec_nth (vec_nth (M p) i) j) U"
  shows "real_analytic_on (\<lambda>p. det (M p)) U"
proof -
  have "real_analytic_on (\<lambda>p. \<Sum>q | q permutes (UNIV::'k set).
          of_int (sign q) * (\<Prod>i\<in>(UNIV::'k set). vec_nth (vec_nth (M p) i) (q i))) U"
    by (intro real_analytic_on_sum[OF U finite_permutations[OF finite]]
              real_analytic_on_mult real_analytic_on_const[OF U]
              real_analytic_on_prod[OF U] E)
  thus ?thesis by (simp add: det_def)
qed

text \<open>Gram-matrix entries expand over any orthonormal basis of the domain:
  the \<open>(i,j)\<close> entry of \<open>matrix (A \<circ> adjoint A)\<close> is \<open>\<Sum>b\<in>Basis (A b $ i)(A b $ j)\<close>.
  This is what makes \<open>mstarg\<close> a polynomial in the (analytic) entry fields.\<close>

lemma matrix_gram_entry:
  fixes A :: "'v::euclidean_space \<Rightarrow> real^'m::finite"
  assumes lin: "linear A"
  shows "vec_nth (vec_nth (matrix (A \<circ> adjoint A)) i) j
       = (\<Sum>b\<in>(Basis::'v set). vec_nth (A b) i * vec_nth (A b) j)"
proof -
  have adj_c: "adjoint A u \<bullet> b = A b \<bullet> u" for u b
    by (metis adjoint_works[OF lin] inner_commute)
  have "vec_nth (vec_nth (matrix (A \<circ> adjoint A)) i) j = vec_nth (A (adjoint A (axis j 1))) i"
    by (simp add: matrix_def)
  also have "\<dots> = A (adjoint A (axis j 1)) \<bullet> axis i 1"
    by (simp add: inner_axis)
  also have "\<dots> = adjoint A (axis j 1) \<bullet> adjoint A (axis i 1)"
    by (simp add: adjoint_works[OF lin])
  also have "\<dots> = (\<Sum>b\<in>(Basis::'v set).
        (adjoint A (axis j 1) \<bullet> b) * (adjoint A (axis i 1) \<bullet> b))"
    by (rule euclidean_inner)
  also have "\<dots> = (\<Sum>b\<in>(Basis::'v set). vec_nth (A b) i * vec_nth (A b) j)"
  proof (rule sum.cong[OF refl])
    fix b assume "b \<in> (Basis::'v set)"
    have "adjoint A (axis j 1) \<bullet> b = vec_nth (A b) j"
      by (simp add: adj_c inner_axis)
    moreover have "adjoint A (axis i 1) \<bullet> b = vec_nth (A b) i"
      by (simp add: adj_c inner_axis)
    ultimately show "(adjoint A (axis j 1) \<bullet> b) * (adjoint A (axis i 1) \<bullet> b)
                   = vec_nth (A b) i * vec_nth (A b) j"
      by (simp add: mult.commute)
  qed
  finally show ?thesis .
qed

subsection \<open>Coordinate access on the joint space\<close>

lemma real_analytic_on_fstJ:
  "real_analytic_on (fst :: planar \<times> ((planar)^'n::finite) \<Rightarrow> planar) UNIV"
  by (rule real_analytic_on_fst[OF open_UNIV])

lemma real_analytic_on_snd_nth:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). vec_nth (snd p) n) UNIV"
  by (rule real_analytic_on_bounded_linear[OF open_UNIV
        bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_snd]])

lemma real_analytic_on_snd_nth_nth:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). vec_nth (vec_nth (snd p) n) k) UNIV"
  by (rule real_analytic_on_bounded_linear[OF open_UNIV
        bounded_linear_compose[OF bounded_linear_vec_nth
          bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_snd]]])

subsection \<open>\<open>phase\<close> and \<open>d_phase\<close>, jointly in \<open>(c,x)\<close>\<close>

lemma real_analytic_on_phase_arg:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). -(fst p \<bullet> vec_nth (snd p) n)) UNIV"
  by (intro real_analytic_on_uminus
        real_analytic_on_inner[OF open_UNIV real_analytic_on_fstJ real_analytic_on_snd_nth])

lemma real_analytic_on_phase:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). phase (fst p) (snd p) n) UNIV"
  unfolding phase_def
  by (rule real_analytic_on_cis[OF real_analytic_on_phase_arg])

lemma real_analytic_on_d_phase:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_phase (fst p) (snd p) h n) UNIV"
proof -
  have sc: "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n). -(fst p \<bullet> vec_nth h n)) UNIV"
    by (intro real_analytic_on_uminus
          real_analytic_on_inner[OF open_UNIV real_analytic_on_fstJ
            real_analytic_on_const[OF open_UNIV]])
  have cx: "real_analytic_on
      (\<lambda>p::planar \<times> ((planar)^'n). \<i> * cis (-(fst p \<bullet> vec_nth (snd p) n))) UNIV"
    by (intro real_analytic_on_cmult[OF open_UNIV] real_analytic_on_const[OF open_UNIV]
          real_analytic_on_cis[OF real_analytic_on_phase_arg])
  show ?thesis
    unfolding d_phase_def
    by (intro real_analytic_on_scaleR_complex[OF open_UNIV] sc cx)
qed

subsection \<open>The six moments, jointly in \<open>(c,x)\<close>\<close>

lemma real_analytic_on_A_moment:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). A_moment (snd p) (fst p)) UNIV"
  unfolding A_moment_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_phase)

lemma real_analytic_on_M1_moment:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). M1_moment (snd p) (fst p)) UNIV"
  unfolding M1_moment_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth] real_analytic_on_phase)

lemma real_analytic_on_M2_moment:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). M2_moment (snd p) (fst p)) UNIV"
  unfolding M2_moment_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth] real_analytic_on_phase)

lemma real_analytic_on_M11_moment:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). M11_moment (snd p) (fst p)) UNIV"
  unfolding M11_moment_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_power[OF real_analytic_on_snd_nth_nth]]
        real_analytic_on_phase)

lemma real_analytic_on_M12_moment:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). M12_moment (snd p) (fst p)) UNIV"
  unfolding M12_moment_def w_M12_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult real_analytic_on_snd_nth_nth
        real_analytic_on_phase)

lemma real_analytic_on_M22_moment:
  "real_analytic_on (\<lambda>p::planar \<times> ((planar)^'n::finite). M22_moment (snd p) (fst p)) UNIV"
  unfolding M22_moment_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_power[OF real_analytic_on_snd_nth_nth]]
        real_analytic_on_phase)

subsection \<open>The six \<open>x\<close>-derivative entries, jointly in \<open>(c,x)\<close> (direction \<open>h\<close> fixed)\<close>

lemma real_analytic_on_d_A_moment_x:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_A_moment_x (snd p) (fst p) h) UNIV"
  unfolding d_A_moment_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_d_phase)

lemma real_analytic_on_d_M1_moment_x:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_M1_moment_x (snd p) (fst p) h) UNIV"
  unfolding d_M1_moment_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV] real_analytic_on_const[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_d_M2_moment_x:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_M2_moment_x (snd p) (fst p) h) UNIV"
  unfolding d_M2_moment_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV] real_analytic_on_const[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_d_M11_moment_x:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_M11_moment_x (snd p) (fst p) h) UNIV"
  unfolding d_M11_moment_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult
        real_analytic_on_const[OF open_UNIV] real_analytic_on_snd_nth_nth
        real_analytic_on_power[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_d_M12_moment_x:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_M12_moment_x (snd p) (fst p) h) UNIV"
  unfolding d_M12_moment_x_def dw_M12_def w_M12_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult
        real_analytic_on_const[OF open_UNIV] real_analytic_on_snd_nth_nth
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_d_M22_moment_x:
  fixes h :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). d_M22_moment_x (snd p) (fst p) h) UNIV"
  unfolding d_M22_moment_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult
        real_analytic_on_const[OF open_UNIV] real_analytic_on_snd_nth_nth
        real_analytic_on_power[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

subsection \<open>The assembled Jacobian components \<open>D*_paper_x\<close> (the \<open>DM_paper_x\<close> in scope)\<close>

text \<open>\<open>Nonemptiness_Paper.DM_paper_x\<close> (the constant \<open>mstarg\<close> is built from --- it shadows
  \<open>Moment_Map.DM_paper_x\<close>) assembles the components \<open>DA_paper_x, \<dots>, DM22_paper_x\<close>,
  whose bodies coincide with the \<open>d_*_moment_x\<close> sums above.\<close>

lemma real_analytic_on_DA_paper_x:
  fixes b :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). DA_paper_x (snd p) (fst p) b) UNIV"
  unfolding DA_paper_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_d_phase)

lemma real_analytic_on_DM1_paper_x:
  fixes b :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). DM1_paper_x (snd p) (fst p) b) UNIV"
  unfolding DM1_paper_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV] real_analytic_on_const[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_DM2_paper_x:
  fixes b :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). DM2_paper_x (snd p) (fst p) b) UNIV"
  unfolding DM2_paper_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV] real_analytic_on_const[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_DM11_paper_x:
  fixes b :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). DM11_paper_x (snd p) (fst p) b) UNIV"
  unfolding DM11_paper_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult
        real_analytic_on_const[OF open_UNIV] real_analytic_on_snd_nth_nth
        real_analytic_on_power[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_DM12_paper_x:
  fixes b :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). DM12_paper_x (snd p) (fst p) b) UNIV"
  unfolding DM12_paper_x_def dw_M12_def w_M12_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult
        real_analytic_on_const[OF open_UNIV] real_analytic_on_snd_nth_nth
        real_analytic_on_phase real_analytic_on_d_phase)

lemma real_analytic_on_DM22_paper_x:
  fixes b :: "(planar)^'n::finite"
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). DM22_paper_x (snd p) (fst p) b) UNIV"
  unfolding DM22_paper_x_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_add
        real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real real_analytic_on_mult
        real_analytic_on_const[OF open_UNIV] real_analytic_on_snd_nth_nth
        real_analytic_on_power[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_phase real_analytic_on_d_phase)

lemma linear_DM_paper_x: "linear (DM_paper_x x c)"
  by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF
        has_derivative_M_paper_x]])

subsection \<open>The \<open>transC\<close>-transported entry fields\<close>

lemma real_analytic_on_transC_DM_entry:
  fixes b :: "(planar)^'n::finite" and i :: 12
  shows "real_analytic_on
           (\<lambda>p::planar \<times> ((planar)^'n). vec_nth (transC (DM_paper_x (snd p) (fst p) b)) i) UNIV"
  using exhaust_12[of i]
  by (elim disjE;
      simp add: transC_def DM_paper_x_def;
      intro real_analytic_on_Re real_analytic_on_Im
        real_analytic_on_DA_paper_x real_analytic_on_DM1_paper_x
        real_analytic_on_DM2_paper_x real_analytic_on_DM11_paper_x
        real_analytic_on_DM12_paper_x real_analytic_on_DM22_paper_x)

subsection \<open>\<open>mstarg\<close> is jointly real-analytic\<close>

text \<open>The definition is verbatim the one in \<open>Nonemptiness_Robust3\<close> (which only needs
  \<open>Moment_Map\<close>/\<open>Moment_Jacobian\<close> constants); when Robust3 imports this bridge layer
  the local copy there is to be deleted in favour of this one.\<close>

definition mstarg :: "planar \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "mstarg c x = det (matrix ((transC \<circ> DM_paper_x x c) \<circ> adjoint (transC \<circ> DM_paper_x x c)))"

lemma linear_transC_DM: "linear (transC \<circ> DM_paper_x x c)"
  by (intro linear_compose linear_DM_paper_x linear_transC)

theorem real_analytic_on_mstarg:
  "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n::finite). mstarg (fst p) (snd p)) UNIV"
proof -
  have entry: "\<And>i j. (\<lambda>p::planar \<times> ((real^2)^'n).
        vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x (snd p) (fst p))
                 \<circ> adjoint (transC \<circ> DM_paper_x (snd p) (fst p)))) i) j)
      = (\<lambda>p. \<Sum>b\<in>(Basis::((real^2)^'n) set).
               vec_nth (transC (DM_paper_x (snd p) (fst p) b)) i
             * vec_nth (transC (DM_paper_x (snd p) (fst p) b)) j)"
    by (rule ext) (simp add: matrix_gram_entry[OF linear_transC_DM])
  have "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n).
          det (matrix ((transC \<circ> DM_paper_x (snd p) (fst p))
                        \<circ> adjoint (transC \<circ> DM_paper_x (snd p) (fst p))))) UNIV"
  proof (rule real_analytic_on_det[OF open_UNIV])
    fix i j :: 12
    show "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n).
            vec_nth (vec_nth (matrix ((transC \<circ> DM_paper_x (snd p) (fst p))
                     \<circ> adjoint (transC \<circ> DM_paper_x (snd p) (fst p)))) i) j) UNIV"
      unfolding entry
      by (intro real_analytic_on_sum[OF open_UNIV finite_Basis] real_analytic_on_mult
            real_analytic_on_transC_DM_entry)
  qed
  thus ?thesis
    unfolding mstarg_def by simp
qed

subsection \<open>Corollaries: the fixed-\<open>c\<close> slice and the \<open>cvec_dip\<close> composition\<close>

lemma real_analytic_on_mstarg_x:
  fixes c :: planar
  shows "real_analytic_on (\<lambda>x::(real^2)^'n::finite. mstarg c x) UNIV"
proof -
  have pair: "real_analytic_on (\<lambda>x::(real^2)^'n. (c, x)) UNIV"
    by (intro real_analytic_on_Pair real_analytic_on_const[OF open_UNIV]
          real_analytic_on_bounded_linear[OF open_UNIV bounded_linear_ident])
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
          (\<lambda>p::planar \<times> ((real^2)^'n). mstarg (fst p) (snd p)) (c, x)) UNIV"
    by (rule real_analytic_on_compose[OF pair real_analytic_on_mstarg subset_UNIV])
  thus ?thesis by simp
qed

lemma real_analytic_on_mstarg_cvec:
  fixes \<omega>0 \<omega>s :: "real^2"
  shows "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
           mstarg (cvec_dip \<omega>0 \<omega>s (snd q)) (fst q)) UNIV"
proof -
  have cv: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2). cvec_dip \<omega>0 \<omega>s (snd q)) UNIV"
    by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
          real_analytic_on_cvec_dip subset_UNIV])
  have pair: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
                (cvec_dip \<omega>0 \<omega>s (snd q), fst q)) UNIV"
    by (intro real_analytic_on_Pair cv real_analytic_on_fst[OF open_UNIV])
  have "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
          (\<lambda>p::planar \<times> ((real^2)^'n). mstarg (fst p) (snd p))
            (cvec_dip \<omega>0 \<omega>s (snd q), fst q)) UNIV"
    by (rule real_analytic_on_compose[OF pair real_analytic_on_mstarg subset_UNIV])
  thus ?thesis by simp
qed

end
