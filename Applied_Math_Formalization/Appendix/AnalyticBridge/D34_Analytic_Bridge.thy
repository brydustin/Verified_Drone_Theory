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


section \<open>Layer 3: the analytic IFT chart engine for the D34 critical graph\<close>

text \<open>At a critical steering angle with nondegenerate \<open>\<omega>\<close>-Hessian, the analytic
  implicit-function theorem produces a REAL-ANALYTIC critical graph \<open>\<omega> = g(x)\<close>, and
  the moment-rank-drop locus along it is the zero set of the real-analytic
  \<open>h x = mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x\<close> --- closed-in-chart and nowhere dense
  UNLESS \<open>h \<equiv> 0\<close> on the (connected) chart.  Contents:
  \<^enum> the 1-D fact that \<open>deriv\<close> of a real-analytic function is real-analytic
    (via the holomorphic extension and \<open>holomorphic_deriv\<close>);
  \<^enum> \<open>cnj\<close>/\<open>cmod\<^sup>2\<close> closure, and joint \<open>(x,\<omega>)\<close>-analyticity of \<open>A_cart\<close>, \<open>dA_cart\<close>
    and hence \<open>gradU (cvec_dip \<omega>0 \<omega>s) gain_dip\<close> via @{thm gradU_explicit} at the
    concrete dipole jets;
  \<^enum> \<open>det \<noteq> 0 \<Longrightarrow> bij\<close> for the Hessian action, and
  \<^enum> the critical-graph dichotomy theorem \<open>dip_critical_graph_dichotomy\<close>.\<close>

subsection \<open>\<open>deriv\<close> of a 1-D real-analytic function is real-analytic\<close>

lemma real_analytic_at_1d_deriv:
  fixes f :: "real \<Rightarrow> real"
  assumes "real_analytic_at_1d f c"
  shows "real_analytic_at_1d (deriv f) c"
proof -
  from assms obtain r g where r0: "0 < r"
    and holo: "g holomorphic_on ball (complex_of_real c) r"
    and agree: "\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow> g (complex_of_real x) = complex_of_real (f x)"
    unfolding real_analytic_at_1d_iff_holo_extension has_holo_extension_at_def by blast
  have key: "deriv g (complex_of_real x) = complex_of_real (deriv f x)"
    if hx: "\<bar>x - c\<bar> < r" for x
  proof -
    have zball: "complex_of_real x \<in> ball (complex_of_real c) r"
      using hx by (simp add: dist_real_def)
    have gder: "(g has_field_derivative deriv g (complex_of_real x))
                  (at (complex_of_real x))"
      by (rule holomorphic_derivI[OF holo open_ball zball])
    have ofr: "((\<lambda>t::real. complex_of_real t) has_derivative complex_of_real) (at x)"
      using bounded_linear.has_derivative[OF bounded_linear_of_real has_derivative_ident]
      by simp
    have comp: "((\<lambda>t. g (complex_of_real t)) has_derivative
                  (\<lambda>h. deriv g (complex_of_real x) * complex_of_real h)) (at x)"
      using has_derivative_compose[OF ofr gder[unfolded has_field_derivative_def]]
      by simp
    have ball_eq: "{t::real. \<bar>t - c\<bar> < r} = ball c r"
      by (auto simp: ball_def dist_real_def)
    have opn: "open {t::real. \<bar>t - c\<bar> < r}"
      by (simp add: ball_eq)
    have xin: "x \<in> {t::real. \<bar>t - c\<bar> < r}" using hx by simp
    have trans: "((\<lambda>t::real. complex_of_real (f t)) has_derivative
                  (\<lambda>h. deriv g (complex_of_real x) * complex_of_real h)) (at x)"
      by (rule has_derivative_transform_within_open[OF comp opn xin])
         (use agree in simp)
    \<comment> \<open>real part: the genuine derivative of \<open>f\<close>\<close>
    have ReD: "((\<lambda>t. Re (complex_of_real (f t))) has_derivative
                (\<lambda>h. Re (deriv g (complex_of_real x) * complex_of_real h))) (at x)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_Re trans])
    have fun_eqR: "(\<lambda>t. Re (complex_of_real (f t))) = f"
      by (rule ext) simp
    have map_eqR: "(\<lambda>h. Re (deriv g (complex_of_real x) * complex_of_real h))
                 = (\<lambda>h. Re (deriv g (complex_of_real x)) * h)"
      by (rule ext) simp
    have fder: "(f has_derivative (\<lambda>h. Re (deriv g (complex_of_real x)) * h)) (at x)"
      using ReD unfolding fun_eqR map_eqR .
    have fRD: "(f has_field_derivative Re (deriv g (complex_of_real x))) (at x)"
      unfolding has_field_derivative_def using fder by (simp add: fun_eq_iff)
    have derivf: "deriv f x = Re (deriv g (complex_of_real x))"
      by (rule DERIV_imp_deriv[OF fRD])
    \<comment> \<open>imaginary part vanishes\<close>
    have ImD: "((\<lambda>t. Im (complex_of_real (f t))) has_derivative
                (\<lambda>h. Im (deriv g (complex_of_real x) * complex_of_real h))) (at x)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_Im trans])
    have fun_eqI: "(\<lambda>t. Im (complex_of_real (f t))) = (\<lambda>t. 0)"
      by (rule ext) simp
    have zder: "((\<lambda>t::real. 0::real) has_derivative (\<lambda>h. 0)) (at x)"
      by (rule has_derivative_const)
    have "(\<lambda>h. Im (deriv g (complex_of_real x) * complex_of_real h)) = (\<lambda>h. 0)"
      by (rule has_derivative_unique[OF ImD[unfolded fun_eqI] zder])
    from fun_cong[OF this, of 1] have Im0: "Im (deriv g (complex_of_real x)) = 0"
      by simp
    show ?thesis
      using derivf Im0 by (simp add: complex_eq_iff)
  qed
  have dholo: "deriv g holomorphic_on ball (complex_of_real c) r"
    by (rule holomorphic_deriv[OF holo open_ball])
  have "\<exists>g'. g' holomorphic_on ball (complex_of_real c) r
           \<and> (\<forall>x. \<bar>x - c\<bar> < r \<longrightarrow> g' (complex_of_real x) = complex_of_real (deriv f x))"
    using dholo key by blast
  thus ?thesis
    unfolding real_analytic_at_1d_iff_holo_extension has_holo_extension_at_def
    by (intro exI[of _ r]) (simp add: r0)
qed

lemma real_analytic_on_deriv_1d:
  fixes f :: "real \<Rightarrow> real"
  assumes "real_analytic_on f U"
  shows "real_analytic_on (deriv f) U"
  using assms unfolding real_analytic_on_1d_iff
  by (simp add: real_analytic_at_1d_deriv)

subsection \<open>\<open>cnj\<close> and \<open>cmod\<^sup>2\<close> closure\<close>

lemma real_analytic_on_cnj:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. cnj (f p)) U"
proof -
  from F have U: "open U" by (simp only: real_analytic_on_def)
  have eq: "(\<lambda>p. cnj (f p)) = (\<lambda>p. Complex (Re (f p)) (- Im (f p)))"
    by (rule ext) (simp add: complex_eq_iff)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_Complex[OF U] real_analytic_on_Re
              real_analytic_on_uminus real_analytic_on_Im F)
qed

lemma real_analytic_on_cmod_sq:
  fixes f :: "'a::euclidean_space \<Rightarrow> complex"
  assumes F: "real_analytic_on f U"
  shows "real_analytic_on (\<lambda>p. (cmod (f p))\<^sup>2) U"
proof -
  have eq: "(\<lambda>p. (cmod (f p))\<^sup>2) = (\<lambda>p. (Re (f p))\<^sup>2 + (Im (f p))\<^sup>2)"
    by (rule ext) (simp add: cmod_power2)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_add real_analytic_on_power
              real_analytic_on_Re real_analytic_on_Im F)
qed

subsection \<open>The dipole gain jet: \<open>deriv gdip\<close> is analytic, and the Fréchet form\<close>

lemma real_analytic_on_deriv_gdip: "real_analytic_on (deriv gdip) UNIV"
  by (rule real_analytic_on_deriv_1d[OF real_analytic_on_gdip])

lemma DERIV_gdip: "DERIV gdip \<theta> :> deriv gdip \<theta>"
proof -
  have "(gdip has_derivative blinfun_apply (Dblinfun gdip \<theta>)) (at \<theta>)"
    by (rule real_analytic_on_has_derivative_Dblinfun[OF real_analytic_on_gdip UNIV_I])
  hence "gdip differentiable at \<theta>" unfolding differentiable_def by blast
  thus ?thesis by (simp add: DERIV_deriv_iff_real_differentiable)
qed

lemma frechet_gdip_eq: "frechet_derivative gdip (at \<theta>) = (*) (deriv gdip \<theta>)"
  by (rule frechet_derivative_at[symmetric])
     (rule DERIV_gdip[unfolded has_field_derivative_def])

subsection \<open>Joint \<open>(x,\<omega>)\<close>-analyticity of \<open>A_cart\<close>, \<open>dA_cart\<close> at the dipole jets\<close>

text \<open>Throughout, the joint point is \<open>q :: ((real^2)^'n) \<times> (real^2)\<close> with \<open>x = fst q\<close>,
  \<open>\<omega> = snd q\<close>.\<close>

lemma real_analytic_on_fst_nth:
  "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2). vec_nth (fst q) n) UNIV"
  by (rule real_analytic_on_bounded_linear[OF open_UNIV
        bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_fst]])

lemma real_analytic_on_cvec_snd:
  "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2). cvec_dip \<omega>0 \<omega>s (snd q)) UNIV"
  by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
        real_analytic_on_cvec_dip subset_UNIV])

lemma real_analytic_on_phase_arg_xo:
  "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
      -(cvec_dip \<omega>0 \<omega>s (snd q) \<bullet> vec_nth (fst q) n)) UNIV"
  by (intro real_analytic_on_uminus
        real_analytic_on_inner[OF open_UNIV real_analytic_on_cvec_snd
          real_analytic_on_fst_nth])

lemma real_analytic_on_A_cart_dip:
  "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
      A_cart (cvec_dip \<omega>0 \<omega>s) (fst q) (snd q)) UNIV"
  unfolding A_cart_def
  by (intro real_analytic_on_sum[OF open_UNIV finite]
        real_analytic_on_cis[OF real_analytic_on_phase_arg_xo])

lemma real_analytic_on_Dcvec_dip_applied:
  fixes h :: "real^2"
  shows "real_analytic_on (\<lambda>\<omega>::real^2. Dcvec_dip \<omega>0 \<omega>s \<omega> h) UNIV"
  unfolding Dcvec_dip_def
  by (intro real_analytic_on_add real_analytic_on_scaleR_vec real_analytic_on_diff
        real_analytic_on_mult real_analytic_on_uminus real_analytic_on_const[OF open_UNIV]
        real_analytic_on_sin_comp real_analytic_on_cos_comp real_analytic_on_vec_nth)

lemma real_analytic_on_dA_cart_dip:
  fixes h :: "real^2"
  shows "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
      dA_cart (cvec_dip \<omega>0 \<omega>s) (Dcvec_dip \<omega>0 \<omega>s (snd q)) (fst q) (snd q) h) UNIV"
proof -
  have Dh: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      Dcvec_dip \<omega>0 \<omega>s (snd q) h) UNIV"
    by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
          real_analytic_on_Dcvec_dip_applied subset_UNIV])
  show ?thesis
    unfolding dA_cart_def
    by (intro real_analytic_on_sum[OF open_UNIV finite]
          real_analytic_on_cmult[OF open_UNIV] real_analytic_on_const[OF open_UNIV]
          real_analytic_on_of_real
          real_analytic_on_inner[OF open_UNIV Dh real_analytic_on_fst_nth]
          real_analytic_on_cis[OF real_analytic_on_phase_arg_xo])
qed

subsection \<open>Joint \<open>(x,\<omega>)\<close>-analyticity of the dipole gradient field\<close>

theorem real_analytic_on_gradU_dip:
  "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) UNIV"
proof -
  have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
        gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q))
      = (\<lambda>q. \<Sum>i\<in>UNIV. dU_cart (cvec_dip \<omega>0 \<omega>s) (Dcvec_dip \<omega>0 \<omega>s (snd q)) gain_dip
              (\<lambda>v. frechet_derivative gdip (at (vec_nth (snd q) 1)) (vec_nth v 1))
              (fst q) (snd q) (axis i 1) *\<^sub>R axis i 1)"
    by (rule ext)
       (rule gradU_explicit[OF has_derivative_cvec_dip gain_dip_has_derivative])
  have dU: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
        dU_cart (cvec_dip \<omega>0 \<omega>s) (Dcvec_dip \<omega>0 \<omega>s (snd q)) gain_dip
          (\<lambda>v. frechet_derivative gdip (at (vec_nth (snd q) 1)) (vec_nth v 1))
          (fst q) (snd q) (axis i 1)) UNIV" for i
  proof -
    have gainq: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
        gain_dip (snd q)) UNIV"
      by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
            real_analytic_on_gain_dip subset_UNIV])
    have sndc: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
        vec_nth (snd q) 1) UNIV"
      by (rule real_analytic_on_bounded_linear[OF open_UNIV
            bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_snd]])
    have dgd: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
        deriv gdip (vec_nth (snd q) 1)) UNIV"
      by (rule real_analytic_on_compose[OF sndc real_analytic_on_deriv_gdip subset_UNIV])
    have fr_eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
          frechet_derivative gdip (at (vec_nth (snd q) 1)) (vec_nth (axis i 1) 1))
        = (\<lambda>q. deriv gdip (vec_nth (snd q) 1) * vec_nth (axis i 1) 1)"
      by (rule ext) (simp add: frechet_gdip_eq)
    have dgain_term: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
        frechet_derivative gdip (at (vec_nth (snd q) 1)) (vec_nth (axis i 1) 1)) UNIV"
      unfolding fr_eq
      by (intro real_analytic_on_mult dgd real_analytic_on_const[OF open_UNIV])
    show ?thesis
      unfolding dU_cart_def
      by (intro real_analytic_on_add real_analytic_on_mult dgain_term
            real_analytic_on_cmod_sq[OF real_analytic_on_A_cart_dip] gainq
            real_analytic_on_const[OF open_UNIV]
            real_analytic_on_Re real_analytic_on_cmult[OF open_UNIV]
            real_analytic_on_cnj[OF real_analytic_on_A_cart_dip]
            real_analytic_on_dA_cart_dip)
  qed
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_sum[OF open_UNIV finite]
          real_analytic_on_scaleR_vec dU)
qed

subsection \<open>\<open>det \<noteq> 0\<close> makes the Hessian action a bijection\<close>

lemma bij_matrix_vector_mult:
  fixes A :: "real^'k^'k::finite"
  assumes dA: "det A \<noteq> 0"
  shows "bij ((*v) A)"
proof -
  from dA have "invertible A" by (simp add: invertible_det_nz)
  then obtain B where AB: "A ** B = mat 1" and BA: "B ** A = mat 1"
    unfolding invertible_def by blast
  show ?thesis
  proof (rule bijI)
    show "inj ((*v) A)"
    proof (rule injI)
      fix u v assume "A *v u = A *v v"
      hence "B *v (A *v u) = B *v (A *v v)" by simp
      thus "u = v"
        by (simp add: matrix_vector_mul_assoc BA matrix_vector_mul_lid)
    qed
    show "surj ((*v) A)"
    proof (rule surjI)
      fix w show "A *v (B *v w) = w"
        by (simp add: matrix_vector_mul_assoc AB matrix_vector_mul_lid)
    qed
  qed
qed

subsection \<open>The critical-graph dichotomy\<close>

text \<open>\<^bold>\<open>The layer-3 engine.\<close>  At any critical point \<open>(x0, \<omega>b)\<close> of the dipole pattern with
  nondegenerate \<open>\<omega>\<close>-Hessian there is a connected open chart \<open>B \<ni> x0\<close> and a REAL-ANALYTIC
  critical graph \<open>g\<close> through \<open>\<omega>b\<close> on which the gradient vanishes identically, and the
  moment-rank-drop locus along the graph either is ALL of \<open>B\<close> (the case the transversality
  witness must exclude) or has closure with empty interior (hence is nowhere dense, and
  meagre-cover material).  Assumes nothing beyond the critical-point data.\<close>

theorem dip_critical_graph_dichotomy:
  fixes x0 :: "(real^2)^'n::finite" and \<omega>b \<omega>0 \<omega>s :: "real^2"
  assumes crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b = 0"
    and nds: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b) \<noteq> 0"
  obtains B g where
    "open B" and "connected B" and "x0 \<in> B" and "g x0 = \<omega>b"
    and "real_analytic_on g B"
    and "\<And>x. x \<in> B \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
    and "(\<forall>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0) \<or>
         interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
proof -
  define F where "F = (\<lambda>p::((real^2)^'n) \<times> (real^2).
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))"
  have Fana: "real_analytic_on F UNIV"
    unfolding F_def by (rule real_analytic_on_gradU_dip)
  have pW: "(x0, \<omega>b) \<in> (UNIV :: (((real^2)^'n) \<times> (real^2)) set)" by simp
  have F0: "F (x0, \<omega>b) = 0" using crit by (simp add: F_def)
  have reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at \<omega>b) \<and> bij L"
  proof (intro exI conjI)
    have "(gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b *v v)) (at \<omega>b)"
      by (rule gradU_dip_has_derivative)
    thus "((\<lambda>y. F (x0, y)) has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b *v v)) (at \<omega>b)"
      by (simp add: F_def)
    show "bij (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b *v v)"
      using bij_matrix_vector_mult[OF nds] by (simp add: o_def)
  qed
  show ?thesis
  proof (rule real_analytic_implicit_function[OF Fana open_UNIV pW F0 reg])
    fix U g
    assume Uo: "open U" and xU: "x0 \<in> U" and gx0: "g x0 = \<omega>b"
      and gana: "real_analytic_on g U"
      and sol: "\<forall>x\<in>U. (x, g x) \<in> UNIV \<and> F (x, g x) = 0"
    obtain \<epsilon> where e0: "0 < \<epsilon>" and esub: "ball x0 \<epsilon> \<subseteq> U"
      using openE[OF Uo xU] by blast
    define B where "B = ball x0 \<epsilon>"
    have Bo: "open B" by (simp add: B_def)
    have Bc: "connected B" by (simp add: B_def)
    have xB: "x0 \<in> B" by (simp add: B_def centre_in_ball e0)
    have Bsub: "B \<subseteq> U" by (simp add: B_def esub)
    have ganaB: "real_analytic_on g B"
      by (rule real_analytic_on_open_subset[OF gana Bo Bsub])
    have zero: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0" if "x \<in> B" for x
      using sol Bsub that by (auto simp: F_def)
    \<comment> \<open>the moment determinant along the graph\<close>
    have idB: "real_analytic_on (\<lambda>x::(real^2)^'n. x) B"
      by (rule real_analytic_on_bounded_linear[OF Bo bounded_linear_ident])
    have pairB: "real_analytic_on (\<lambda>x::(real^2)^'n. (x, g x)) B"
      by (rule real_analytic_on_Pair[OF idB ganaB])
    have "real_analytic_on (\<lambda>x::(real^2)^'n.
            (\<lambda>q::((real^2)^'n) \<times> (real^2). mstarg (cvec_dip \<omega>0 \<omega>s (snd q)) (fst q))
              (x, g x)) B"
      by (rule real_analytic_on_compose[OF pairB real_analytic_on_mstarg_cvec subset_UNIV])
    hence hana: "real_analytic_on (\<lambda>x. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x) B"
      by simp
    have dich: "(\<forall>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0) \<or>
         interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
    proof (cases "\<forall>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0")
      case True thus ?thesis by blast
    next
      case False
      hence "\<exists>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0" by blast
      from real_analytic_nowhere_dense_zeros[OF hana Bc this]
      show ?thesis by blast
    qed
    show thesis
      by (rule that[OF Bo Bc xB gx0 ganaB zero dich])
  qed
qed


section \<open>Layer 4a: the analytic implicit function theorem WITH a uniqueness neighbourhood\<close>

text \<open>@{thm real_analytic_implicit_function} produces the solution graph but does not
  expose the neighbourhood on which the graph is the ONLY zero locus --- which the D34
  covering argument needs (bad points near a chart must lie ON the graph).  This variant
  mirrors the assembly proof verbatim and additionally returns the local-inverse
  neighbourhood \<open>N\<close> (the domain of the homeomorphism \<open>\<Phi>(x,y) = (x, F(x,y))\<close>): every
  zero of \<open>F\<close> in \<open>N\<close> over a base point of \<open>U\<close> lies on the graph, by injectivity of
  \<open>\<Phi>\<close> on \<open>N\<close>.  Upstream candidate for \<open>Real_Analytic_IFT\<close>.\<close>

theorem real_analytic_implicit_function_unique:
  fixes F :: "('a::euclidean_space \<times> 'b::euclidean_space) \<Rightarrow> 'b"
  assumes ana: "real_analytic_on F W"
    and Wopen: "open W"
    and pW: "(x0, y0) \<in> W"
    and F0: "F (x0, y0) = 0"
    and reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at y0) \<and> bij L"
  obtains U N g where
      "open U" and "x0 \<in> U" and "open N" and "(x0, y0) \<in> N" and "N \<subseteq> W"
      and "g x0 = y0"
      and "real_analytic_on g U"
      and "\<forall>x\<in>U. (x, g x) \<in> N \<and> F (x, g x) = 0"
      and "\<forall>x\<in>U. \<forall>y. (x, y) \<in> N \<longrightarrow> F (x, y) = 0 \<longrightarrow> y = g x"
proof -
  let ?Phi = "\<lambda>p::'a \<times> 'b. (fst p, F p)"
  let ?p0 = "(x0, y0)"
  obtain L where Lder: "((\<lambda>y. F (x0, y)) has_derivative L) (at y0)"
    and bijL: "bij L"
    using reg by blast

  have Phi_ana: "real_analytic_on ?Phi W"
    by (rule real_analytic_on_Pair[OF real_analytic_on_fst[OF Wopen] ana])

  have C1_F: "Ck_at (Suc 0) F ?p0"
    using real_analytic_imp_Cinfinity[OF ana] pW
    unfolding Cinfinity_on_def Cinfinity_at_def
    by blast
  hence Fdiff: "F differentiable at ?p0"
    by (simp only: Ck_at.simps(2))
  then obtain A where Fder: "(F has_derivative A) (at ?p0)"
    unfolding differentiable_def by blast

  have slice_der: "((\<lambda>y. F (x0, y)) has_derivative (\<lambda>dy. A (0, dy))) (at y0)"
  proof -
    have pair_der: "((\<lambda>y. (x0, y)) has_derivative (\<lambda>dy. (0, dy))) (at y0)"
    proof -
      have cder: "((\<lambda>y::'b. x0) has_derivative (\<lambda>dy. 0)) (at y0)"
        by (rule has_derivative_const)
      have idder: "((\<lambda>y::'b. y) has_derivative (\<lambda>dy. dy)) (at y0)"
        by (rule has_derivative_ident)
      show ?thesis
        using has_derivative_Pair[OF cder idder] by simp
    qed
    show ?thesis
      using has_derivative_compose[OF pair_der Fder] by simp
  qed
  have L_eq: "L = (\<lambda>dy. A (0, dy))"
    by (rule has_derivative_unique[OF Lder slice_der])

  let ?B = "\<lambda>h::'a \<times> 'b. (fst h, A h)"
  have Phi_der: "(?Phi has_derivative ?B) (at ?p0)"
  proof -
    have fst_der: "((fst :: ('a \<times> 'b) \<Rightarrow> 'a) has_derivative fst) (at ?p0)"
      by (rule bounded_linear.has_derivative[OF bounded_linear_fst has_derivative_ident])
    show ?thesis
      using has_derivative_Pair[OF fst_der Fder] by simp
  qed

  have blA: "bounded_linear A"
    using Fder by (rule has_derivative_bounded_linear)
  interpret A: bounded_linear A by (rule blA)
  have surjL: "surj L" and injL: "inj L"
    using bijL by (auto simp: bij_def)

  let ?C = "\<lambda>q::'a \<times> 'b. (fst q, (inv_into UNIV L) (snd q - A (fst q, 0)))"
  have B_C: "?B (?C q) = q" for q
  proof -
    let ?w = "snd q - A (fst q, 0)"
    have decomp: "(fst q, (inv_into UNIV L) ?w) = (fst q, 0) + (0, (inv_into UNIV L) ?w)"
      by simp
    have Aq: "A (fst q, (inv_into UNIV L) ?w) = A (fst q, 0) + A (0, (inv_into UNIV L) ?w)"
      by (subst decomp) (rule A.add)
    have A0_inv: "A (0, (inv_into UNIV L) ?w) = ?w"
    proof -
      have "A (0, (inv_into UNIV L) ?w) = L ((inv_into UNIV L) ?w)"
        using L_eq by simp
      also have "... = ?w"
        using surjL by (rule surj_f_inv_f)
      finally show ?thesis .
    qed
    have Aeq: "A (fst q, (inv_into UNIV L) ?w) = snd q"
      using Aq A0_inv by simp
    show ?thesis
      using Aeq
      by simp
  qed
  have C_B: "?C (?B h) = h" for h
  proof -
    have Ah: "A h = A (fst h, 0) + A (0, snd h)"
    proof -
      have decomp: "h = (fst h, 0) + (0, snd h)"
        by simp
      show ?thesis
        by (subst decomp) (rule A.add)
    qed
    have "A h - A (fst h, 0) = L (snd h)"
      using Ah L_eq by simp
    thus ?thesis
      using injL by (simp add: inv_f_f)
  qed
  have bijB: "bij ?B"
  proof (rule bijI)
    show "inj ?B"
    proof (rule injI)
      fix x y :: "'a \<times> 'b"
      assume "?B x = ?B y"
      hence H: "?C (?B x) = ?C (?B y)"
        by simp
      have Cx: "?C (?B x) = x"
        by (rule C_B)
      have Cy: "?C (?B y) = y"
        by (rule C_B)
      show "x = y"
        using H Cx Cy by metis
    qed
    show "surj ?B"
      unfolding surj_def
    proof
      fix y :: "'a \<times> 'b"
      have "?B (?C y) = y"
        by (rule B_C)
      hence "y = ?B (?C y)"
        by simp
      show "\<exists>x. y = ?B x"
        using \<open>y = ?B (?C y)\<close> by blast
    qed
  qed

  obtain U' V Psi where U'_open: "open U'" and p0_U': "?p0 \<in> U'"
    and U'_sub: "U' \<subseteq> W" and V_open: "open V"
    and Phi_p0_V: "?Phi ?p0 \<in> V"
    and homeo: "homeomorphism U' V ?Phi Psi"
    and Psi_ana: "real_analytic_on Psi V"
  proof (rule real_analytic_local_inverse[OF Phi_ana Wopen pW])
    show "\<exists>L. (?Phi has_derivative L) (at ?p0) \<and> bij L"
      using Phi_der bijB by blast
  qed blast

  define U where "U = {x. (x, 0::'b) \<in> V}"
  define g where "g = (\<lambda>x. snd (Psi (x, 0::'b)))"

  have U_open: "open U"
  proof -
    have cont_slice: "continuous_on UNIV (\<lambda>x::'a. (x, 0::'b))"
      by (intro continuous_intros)
    have "open (UNIV \<inter> (\<lambda>x::'a. (x, 0::'b)) -` V)"
      by (rule continuous_open_preimage[OF cont_slice open_UNIV V_open])
    thus ?thesis
      by (simp add: U_def vimage_def)
  qed
  have x0_U: "x0 \<in> U"
    using Phi_p0_V F0 by (simp add: U_def)
  have g_x0: "g x0 = y0"
    using homeomorphism_apply1[OF homeo p0_U'] F0
    by (simp add: g_def)

  have slice_ana: "real_analytic_on (\<lambda>x::'a. (x, 0::'b)) U"
    by (rule real_analytic_on_Pair_const[OF U_open])
  have slice_image: "(\<lambda>x::'a. (x, 0::'b)) ` U \<subseteq> V"
    by (auto simp: U_def)
  have Psi_slice_ana: "real_analytic_on (\<lambda>x::'a. Psi (x, 0::'b)) U"
    using real_analytic_on_compose[OF slice_ana Psi_ana slice_image] by simp
  have g_ana: "real_analytic_on g U"
  proof -
    have snd_ana: "real_analytic_on (snd :: ('a \<times> 'b) \<Rightarrow> 'b) UNIV"
      by (rule real_analytic_on_snd) simp
    have "real_analytic_on (\<lambda>x::'a. snd (Psi (x, 0::'b))) U"
      by (rule real_analytic_on_compose[OF Psi_slice_ana snd_ana]) simp
    thus ?thesis
      by (simp add: g_def)
  qed

  have solution: "\<forall>x\<in>U. (x, g x) \<in> W \<and> F (x, g x) = 0"
  proof
    fix x assume xU: "x \<in> U"
    have x0V: "(x, 0::'b) \<in> V"
      using xU by (simp add: U_def)
    have Psi_in: "Psi (x, 0::'b) \<in> U'"
      using homeomorphism_image2[OF homeo] x0V by blast
    have Phi_Psi: "?Phi (Psi (x, 0::'b)) = (x, 0::'b)"
      by (rule homeomorphism_apply2[OF homeo x0V])
    have fst_Psi: "fst (Psi (x, 0::'b)) = x"
      using Phi_Psi by simp
    have F_Psi: "F (Psi (x, 0::'b)) = 0"
      using Phi_Psi by simp
    have "(x, g x) = Psi (x, 0::'b)"
      using fst_Psi by (simp add: g_def prod_eq_iff)
    thus "(x, g x) \<in> W \<and> F (x, g x) = 0"
      using Psi_in U'_sub F_Psi by auto
  qed

  have solutionN: "\<forall>x\<in>U. (x, g x) \<in> U' \<and> F (x, g x) = 0"
  proof
    fix x assume xU: "x \<in> U"
    have x0V: "(x, 0::'b) \<in> V"
      using xU by (simp add: U_def)
    have Psi_in: "Psi (x, 0::'b) \<in> U'"
      using homeomorphism_image2[OF homeo] x0V by blast
    have Phi_Psi: "?Phi (Psi (x, 0::'b)) = (x, 0::'b)"
      by (rule homeomorphism_apply2[OF homeo x0V])
    have fst_Psi: "fst (Psi (x, 0::'b)) = x"
      using Phi_Psi by simp
    have F_Psi: "F (Psi (x, 0::'b)) = 0"
      using Phi_Psi by simp
    have "(x, g x) = Psi (x, 0::'b)"
      using fst_Psi by (simp add: g_def prod_eq_iff)
    thus "(x, g x) \<in> U' \<and> F (x, g x) = 0"
      using Psi_in F_Psi by auto
  qed

  have unique: "\<forall>x\<in>U. \<forall>y. (x, y) \<in> U' \<longrightarrow> F (x, y) = 0 \<longrightarrow> y = g x"
  proof (intro ballI allI impI)
    fix x :: 'a and y :: 'b
    assume xU: "x \<in> U" and xyU': "(x, y) \<in> U'" and Fxy: "F (x, y) = 0"
    have x0V: "(x, 0::'b) \<in> V"
      using xU by (simp add: U_def)
    have Phi_Psi: "?Phi (Psi (x, 0::'b)) = (x, 0::'b)"
      by (rule homeomorphism_apply2[OF homeo x0V])
    have gx_eq: "(x, g x) = Psi (x, 0::'b)"
      using Phi_Psi by (simp add: g_def prod_eq_iff)
    have Phi_xy: "?Phi (x, y) = (x, 0::'b)"
      using Fxy by simp
    have "Psi (?Phi (x, y)) = (x, y)"
      by (rule homeomorphism_apply1[OF homeo xyU'])
    hence "Psi (x, 0::'b) = (x, y)"
      using Phi_xy by simp
    with gx_eq have "(x, g x) = (x, y)" by simp
    thus "y = g x" by simp
  qed

  show ?thesis
    by (rule that[OF U_open x0_U U'_open p0_U' U'_sub g_x0 g_ana solutionN unique])
qed

section \<open>The critical-graph dichotomy WITH local uniqueness\<close>

text \<open>\<^bold>\<open>The complete layer-3/4a engine.\<close>  As @{thm dip_critical_graph_dichotomy}, but
  additionally exposing the uniqueness neighbourhood \<open>N \<ni> (x0, \<omega>b)\<close>: every critical
  point \<open>(x, \<omega>) \<in> N\<close> with \<open>x \<in> B\<close> lies ON the graph, \<open>\<omega> = g x\<close>.  This is what lets a
  chart capture ALL bad points near it in the D34 covering argument.\<close>

theorem dip_critical_graph_dichotomy_unique:
  fixes x0 :: "(real^2)^'n::finite" and \<omega>b \<omega>0 \<omega>s :: "real^2"
  assumes crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b = 0"
    and nds: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b) \<noteq> 0"
  obtains B N g where
    "open B" and "connected B" and "x0 \<in> B"
    and "open N" and "(x0, \<omega>b) \<in> N"
    and "g x0 = \<omega>b" and "real_analytic_on g B"
    and "\<And>x. x \<in> B \<Longrightarrow>
           (x, g x) \<in> N \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
    and "\<And>x \<omega>. x \<in> B \<Longrightarrow> (x, \<omega>) \<in> N \<Longrightarrow>
           gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<Longrightarrow> \<omega> = g x"
    and "(\<forall>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0) \<or>
         interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
proof -
  define F where "F = (\<lambda>p::((real^2)^'n) \<times> (real^2).
      gradU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst p) (snd p))"
  have Fana: "real_analytic_on F UNIV"
    unfolding F_def by (rule real_analytic_on_gradU_dip)
  have pW: "(x0, \<omega>b) \<in> (UNIV :: (((real^2)^'n) \<times> (real^2)) set)" by simp
  have F0: "F (x0, \<omega>b) = 0" using crit by (simp add: F_def)
  have reg: "\<exists>L. ((\<lambda>y. F (x0, y)) has_derivative L) (at \<omega>b) \<and> bij L"
  proof (intro exI conjI)
    have "(gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b *v v)) (at \<omega>b)"
      by (rule gradU_dip_has_derivative)
    thus "((\<lambda>y. F (x0, y)) has_derivative
            (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b *v v)) (at \<omega>b)"
      by (simp add: F_def)
    show "bij (\<lambda>v. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b *v v)"
      using bij_matrix_vector_mult[OF nds] by (simp add: o_def)
  qed
  show ?thesis
  proof (rule real_analytic_implicit_function_unique[OF Fana open_UNIV pW F0 reg])
    fix U N g
    assume Uo: "open U" and xU: "x0 \<in> U"
      and Nopen: "open N" and pN: "(x0, \<omega>b) \<in> N" and NW: "N \<subseteq> UNIV"
      and gx0: "g x0 = \<omega>b"
      and gana: "real_analytic_on g U"
      and sol: "\<forall>x\<in>U. (x, g x) \<in> N \<and> F (x, g x) = 0"
      and uniq: "\<forall>x\<in>U. \<forall>y. (x, y) \<in> N \<longrightarrow> F (x, y) = 0 \<longrightarrow> y = g x"
    obtain \<epsilon> where e0: "0 < \<epsilon>" and esub: "ball x0 \<epsilon> \<subseteq> U"
      using openE[OF Uo xU] by blast
    define B where "B = ball x0 \<epsilon>"
    have Bo: "open B" by (simp add: B_def)
    have Bc: "connected B" by (simp add: B_def)
    have xB: "x0 \<in> B" by (simp add: B_def centre_in_ball e0)
    have Bsub: "B \<subseteq> U" by (simp add: B_def esub)
    have ganaB: "real_analytic_on g B"
      by (rule real_analytic_on_open_subset[OF gana Bo Bsub])
    have graphB: "(x, g x) \<in> N \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
      if "x \<in> B" for x
      using sol Bsub that by (auto simp: F_def)
    have uniqB: "\<omega> = g x"
      if "x \<in> B" and "(x, \<omega>) \<in> N" and "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      for x \<omega>
      using uniq Bsub that by (auto simp: F_def)
    have idB: "real_analytic_on (\<lambda>x::(real^2)^'n. x) B"
      by (rule real_analytic_on_bounded_linear[OF Bo bounded_linear_ident])
    have pairB: "real_analytic_on (\<lambda>x::(real^2)^'n. (x, g x)) B"
      by (rule real_analytic_on_Pair[OF idB ganaB])
    have "real_analytic_on (\<lambda>x::(real^2)^'n.
            (\<lambda>q::((real^2)^'n) \<times> (real^2). mstarg (cvec_dip \<omega>0 \<omega>s (snd q)) (fst q))
              (x, g x)) B"
      by (rule real_analytic_on_compose[OF pairB real_analytic_on_mstarg_cvec subset_UNIV])
    hence hana: "real_analytic_on (\<lambda>x. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x) B"
      by simp
    have dich: "(\<forall>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0) \<or>
         interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
    proof (cases "\<forall>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0")
      case True thus ?thesis by blast
    next
      case False
      hence "\<exists>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0" by blast
      from real_analytic_nowhere_dense_zeros[OF hana Bc this]
      show ?thesis by blast
    qed
    show thesis
      by (rule that[OF Bo Bc xB Nopen pN gx0 ganaB graphB uniqB dich])
  qed
qed


section \<open>Layer 4b, \<open>wit_core\<close> substrate: the Hessian entry fields are real-analytic\<close>

text \<open>The Case-B branches split on the entries of the \<open>\<omega>\<close>-Hessian along the critical
  graph, and Case B lives on \<open>H \<not>\<equiv> 0\<close> (supplied by \<open>det HessU \<noteq> 0\<close>, which the engine
  holds at the basepoint).  This theory proves that the three Hessian entry fields
  and \<open>det HessU\<close> are real-analytic JOINTLY in \<open>(x,\<omega>)\<close>, via the formalized moment
  dictionary @{thm HessU_dip_entry_moments}: the substrate for (i) threading
  \<open>det HessU \<noteq> 0\<close> along charts by a continuity shrink and (ii) the branch
  certificates, which differentiate exactly these fields.\<close>

subsection \<open>Component and quadratic-form helpers\<close>

lemma real_analytic_on_field_nth:
  fixes F :: "'a::euclidean_space \<Rightarrow> real^'k::finite"
  assumes F: "real_analytic_on F U"
  shows "real_analytic_on (\<lambda>q. vec_nth (F q) j) U"
proof -
  have "real_analytic_on (\<lambda>q. F q \<bullet> axis j 1) U"
    by (rule real_analytic_on_inner_component[OF F])
  moreover have "(\<lambda>q. F q \<bullet> axis j 1) = (\<lambda>q. vec_nth (F q) j)"
    by (rule ext) (simp add: inner_axis)
  ultimately show ?thesis by simp
qed

lemma inner_expand_vec:
  fixes a b :: "real^'k::finite"
  shows "a \<bullet> b = (\<Sum>i\<in>UNIV. vec_nth a i * vec_nth b i)"
  by (simp add: inner_vec_def)

lemma inner_mv_expand:
  fixes a b :: "real^'k::finite" and M :: "real^'k^'k"
  shows "a \<bullet> (M *v b)
       = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. vec_nth a i * (vec_nth (vec_nth M i) j * vec_nth b j))"
  by (simp add: inner_vec_def matrix_vector_mult_def sum_distrib_left)

subsection \<open>The \<open>c\<close>-pattern moment fields, jointly in \<open>(c,x)\<close>\<close>

lemma real_analytic_on_Afun_cx:
  "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n::finite). Afun (snd p) (fst p)) UNIV"
  unfolding Afun_def
  by (intro real_analytic_on_sum[OF open_UNIV finite]
        real_analytic_on_cis[OF real_analytic_on_phase_arg])

lemma real_analytic_on_Mcfun_cx:
  "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n::finite). Mcfun (snd p) (fst p) k) UNIV"
  unfolding Mcfun_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_cis[OF real_analytic_on_phase_arg])

lemma real_analytic_on_M2cfun_cx:
  "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n::finite). M2cfun (snd p) (fst p) k l) UNIV"
  unfolding M2cfun_def
  by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_cmult[OF open_UNIV]
        real_analytic_on_of_real[OF real_analytic_on_snd_nth_nth]
        real_analytic_on_cis[OF real_analytic_on_phase_arg])

subsection \<open>\<open>Hcmat\<close> entries and the \<open>c\<close>-pattern gradient components, jointly in \<open>(c,x)\<close>\<close>

lemma Hcmat_entry_eq:
  "vec_nth (vec_nth (Hcmat x c) k) l
     = 2 * (Re (cnj (Mcfun x c l) * Mcfun x c k) - Re (cnj (Afun x c) * M2cfun x c k l))"
  by (simp add: Hcmat_def)

lemma real_analytic_on_Hcmat_entry_cx:
  "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n::finite).
      vec_nth (vec_nth (Hcmat (snd p) (fst p)) k) l) UNIV"
proof -
  have eq: "(\<lambda>p::planar \<times> ((real^2)^'n).
      vec_nth (vec_nth (Hcmat (snd p) (fst p)) k) l)
    = (\<lambda>p. 2 * (Re (cnj (Mcfun (snd p) (fst p) l) * Mcfun (snd p) (fst p) k)
              - Re (cnj (Afun (snd p) (fst p)) * M2cfun (snd p) (fst p) k l)))"
    by (rule ext) (simp add: Hcmat_entry_eq)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_diff real_analytic_on_Re real_analytic_on_cmult[OF open_UNIV]
          real_analytic_on_cnj real_analytic_on_Mcfun_cx real_analytic_on_Afun_cx
          real_analytic_on_M2cfun_cx)
qed

lemma real_analytic_on_gradUc_comp_cx:
  "real_analytic_on (\<lambda>p::planar \<times> ((real^2)^'n::finite).
      vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) (snd p) (fst p)) j) UNIV"
proof -
  have eq: "(\<lambda>p::planar \<times> ((real^2)^'n).
      vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) (snd p) (fst p)) j)
    = (\<lambda>p. 2 * (Re (Afun (snd p) (fst p)) * Im (Mcfun (snd p) (fst p) j)
              - Im (Afun (snd p) (fst p)) * Re (Mcfun (snd p) (fst p) j)))"
    by (rule ext) (simp add: gradU_c_field)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
          real_analytic_on_diff real_analytic_on_Re real_analytic_on_Im
          real_analytic_on_Afun_cx real_analytic_on_Mcfun_cx)
qed

subsection \<open>The gain's second derivative\<close>

lemma real_analytic_on_deriv2_gdip: "real_analytic_on (deriv (deriv gdip)) UNIV"
  by (rule real_analytic_on_deriv_1d[OF real_analytic_on_deriv_gdip])

lemma DERIV_deriv_gdip: "DERIV (deriv gdip) \<theta> :> deriv (deriv gdip) \<theta>"
proof -
  have "(deriv gdip has_derivative blinfun_apply (Dblinfun (deriv gdip) \<theta>)) (at \<theta>)"
    by (rule real_analytic_on_has_derivative_Dblinfun[OF real_analytic_on_deriv_gdip UNIV_I])
  hence "deriv gdip differentiable at \<theta>" unfolding differentiable_def by blast
  thus ?thesis by (simp add: DERIV_deriv_iff_real_differentiable)
qed

lemma frechet_gdip2_eq:
  "frechet_derivative (\<lambda>\<eta>::real^2. frechet_derivative gdip (at (vec_nth \<eta> 1)) c) (at \<omega>)
   = (\<lambda>v. deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * c)"
proof -
  have fun_eq: "(\<lambda>\<eta>::real^2. frechet_derivative gdip (at (vec_nth \<eta> 1)) c)
              = (\<lambda>\<eta>. deriv gdip (vec_nth \<eta> 1) * c)"
    by (rule ext) (simp add: frechet_gdip_eq)
  have hv: "((\<lambda>\<eta>::real^2. vec_nth \<eta> 1) has_derivative (\<lambda>v. vec_nth v 1)) (at \<omega>)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_ident])
  have hd: "((\<lambda>\<eta>::real^2. deriv gdip (vec_nth \<eta> 1)) has_derivative
              (\<lambda>v. deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1)) (at \<omega>)"
    using has_derivative_compose[OF hv
        DERIV_deriv_gdip[unfolded has_field_derivative_def, of "vec_nth \<omega> 1"]]
    by simp
  have hdc: "((\<lambda>\<eta>::real^2. deriv gdip (vec_nth \<eta> 1) * c) has_derivative
              (\<lambda>v. deriv (deriv gdip) (vec_nth \<omega> 1) * vec_nth v 1 * c)) (at \<omega>)"
    using bounded_linear.has_derivative[OF bounded_linear_mult_left hd] by simp
  show ?thesis
    unfolding fun_eq
    by (rule frechet_derivative_at[symmetric, OF hdc])
qed

subsection \<open>The second chart jet, applied\<close>

lemma real_analytic_on_D2cvec_dip_applied:
  fixes h h' :: "real^2"
  shows "real_analytic_on (\<lambda>\<omega>::real^2. D2cvec_dip \<omega>0 \<omega>s \<omega> h h') UNIV"
  unfolding D2cvec_dip_def
  by (intro real_analytic_on_add real_analytic_on_scaleR_vec real_analytic_on_diff
        real_analytic_on_mult real_analytic_on_uminus real_analytic_on_const[OF open_UNIV]
        real_analytic_on_sin_comp real_analytic_on_cos_comp real_analytic_on_vec_nth)

subsection \<open>Assembly: the Hessian entry fields\<close>

theorem real_analytic_on_HessU_dip_entry:
  fixes k l :: 2
  shows "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) k) l) UNIV"
proof -
  \<comment> \<open>the swap into the \<open>(c,x)\<close> frame\<close>
  have sig: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      (cvec_dip \<omega>0 \<omega>s (snd q), fst q)) UNIV"
    by (intro real_analytic_on_Pair
          real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
            real_analytic_on_cvec_dip subset_UNIV]
          real_analytic_on_fst[OF open_UNIV])
  \<comment> \<open>vector fields along the chart jet\<close>
  have Dc: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      Dcvec_dip \<omega>0 \<omega>s (snd q) h) UNIV" for h
    by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
          real_analytic_on_Dcvec_dip_applied subset_UNIV])
  have D2c: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      D2cvec_dip \<omega>0 \<omega>s (snd q) h h') UNIV" for h h'
    by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
          real_analytic_on_D2cvec_dip_applied subset_UNIV])
  \<comment> \<open>scalar fields through the swap\<close>
  have hcE: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      vec_nth (vec_nth (Hcmat (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) i) j) UNIV" for i j
    using real_analytic_on_compose[OF sig real_analytic_on_Hcmat_entry_cx subset_UNIV]
    by simp
  have gcC: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) i) UNIV" for i
    using real_analytic_on_compose[OF sig real_analytic_on_gradUc_comp_cx subset_UNIV]
    by simp
  have gain: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2). gain_dip (snd q)) UNIV"
    by (rule real_analytic_on_compose[OF real_analytic_on_snd[OF open_UNIV]
          real_analytic_on_gain_dip subset_UNIV])
  \<comment> \<open>term 1: the curvature quadratic form\<close>
  have T1: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      Dcvec_dip \<omega>0 \<omega>s (snd q) (axis k 1)
        \<bullet> (Hcmat (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)) *v Dcvec_dip \<omega>0 \<omega>s (snd q) (axis l 1))) UNIV"
  proof -
    have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
        Dcvec_dip \<omega>0 \<omega>s (snd q) (axis k 1)
          \<bullet> (Hcmat (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)) *v Dcvec_dip \<omega>0 \<omega>s (snd q) (axis l 1)))
      = (\<lambda>q. \<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV.
            vec_nth (Dcvec_dip \<omega>0 \<omega>s (snd q) (axis k 1)) i
          * (vec_nth (vec_nth (Hcmat (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) i) j
             * vec_nth (Dcvec_dip \<omega>0 \<omega>s (snd q) (axis l 1)) j))"
      by (rule ext) (rule inner_mv_expand)
    show ?thesis
      unfolding eq
      by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_mult
            real_analytic_on_field_nth[OF Dc] hcE)
  qed
  \<comment> \<open>term 2 pattern: inner products against the \<open>c\<close>-gradient\<close>
  have T2: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      F q \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) UNIV"
    if F: "real_analytic_on F UNIV" for F :: "((real^2)^'n) \<times> (real^2) \<Rightarrow> real^2"
  proof -
    have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
        F q \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)))
      = (\<lambda>q. \<Sum>i\<in>UNIV. vec_nth (F q) i
           * vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) i)"
      by (rule ext) (rule inner_expand_vec)
    show ?thesis
      unfolding eq
      by (intro real_analytic_on_sum[OF open_UNIV finite] real_analytic_on_mult
            real_analytic_on_field_nth[OF F] gcC)
  qed
  \<comment> \<open>gain derivative fields\<close>
  have G1: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      frechet_derivative gdip (at (vec_nth (snd q) 1)) c) UNIV" for c
  proof -
    have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
        frechet_derivative gdip (at (vec_nth (snd q) 1)) c)
      = (\<lambda>q. deriv gdip (vec_nth (snd q) 1) * c)"
      by (rule ext) (simp add: frechet_gdip_eq)
    have snd1: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2). vec_nth (snd q) 1) UNIV"
      by (rule real_analytic_on_bounded_linear[OF open_UNIV
            bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_snd]])
    show ?thesis
      unfolding eq
      by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
            real_analytic_on_compose[OF snd1 real_analytic_on_deriv_gdip subset_UNIV])
  qed
  have G2: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) c)
        (at (snd q)) v) UNIV" for c v
  proof -
    have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
        frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) c)
          (at (snd q)) v)
      = (\<lambda>q. deriv (deriv gdip) (vec_nth (snd q) 1) * vec_nth v 1 * c)"
      by (rule ext) (simp add: frechet_gdip2_eq)
    have snd1: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2). vec_nth (snd q) 1) UNIV"
      by (rule real_analytic_on_bounded_linear[OF open_UNIV
            bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_snd]])
    show ?thesis
      unfolding eq
      by (intro real_analytic_on_mult real_analytic_on_const[OF open_UNIV]
            real_analytic_on_compose[OF snd1 real_analytic_on_deriv2_gdip subset_UNIV])
  qed
  \<comment> \<open>the pattern value\<close>
  have UC: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
      U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) UNIV"
  proof -
    have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
        U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)))
      = (\<lambda>q. (cmod (Afun (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))))\<^sup>2)"
      by (rule ext) (simp add: U_cart_def A_cart_eq_Afun)
    have Af: "real_analytic_on (\<lambda>q::((real^2)^'n) \<times> (real^2).
        Afun (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))) UNIV"
      using real_analytic_on_compose[OF sig real_analytic_on_Afun_cx subset_UNIV]
      by simp
    show ?thesis
      unfolding eq by (rule real_analytic_on_cmod_sq[OF Af])
  qed
  \<comment> \<open>final assembly through the moment dictionary\<close>
  have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) k) l)
    = (\<lambda>q. (gain_dip (snd q) * (Dcvec_dip \<omega>0 \<omega>s (snd q) (axis k 1)
              \<bullet> (Hcmat (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)) *v (Dcvec_dip \<omega>0 \<omega>s (snd q) (axis l 1)))
            + (D2cvec_dip \<omega>0 \<omega>s (snd q) (axis k 1) (axis l 1))
              \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)))
        + frechet_derivative gdip (at (vec_nth (snd q) 1)) (vec_nth (axis l 1) 1)
            * (Dcvec_dip \<omega>0 \<omega>s (snd q) (axis k 1)
               \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))))
      + (frechet_derivative gdip (at (vec_nth (snd q) 1)) (vec_nth (axis k 1) 1)
            * (Dcvec_dip \<omega>0 \<omega>s (snd q) (axis l 1)
               \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q)))
        + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1) 1))
            (at (snd q)) (axis l 1)
            * U_cart (\<lambda>c. c) (\<lambda>_. 1) (fst q) (cvec_dip \<omega>0 \<omega>s (snd q))))"
    by (rule ext) (rule HessU_dip_entry_moments)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_add real_analytic_on_mult gain T1 T2 Dc D2c G1 G2 UC)
qed

subsection \<open>The Hessian determinant field\<close>

theorem real_analytic_on_detHessU_dip:
  "real_analytic_on (\<lambda>q::((real^2)^'n::finite) \<times> (real^2).
      det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q))) UNIV"
proof -
  have eq: "(\<lambda>q::((real^2)^'n) \<times> (real^2).
      det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)))
    = (\<lambda>q. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) 1) 1
         * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) 2) 2
         - vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) 1) 2
         * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) 2) 1)"
    by (rule ext) (rule det_2)
  show ?thesis
    unfolding eq
    by (intro real_analytic_on_diff real_analytic_on_mult real_analytic_on_HessU_dip_entry)
qed

lemma real_analytic_on_detHessU_chart:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2"
  assumes Bo: "open B" and gana: "real_analytic_on g B"
  shows "real_analytic_on (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) B"
proof -
  have idB: "real_analytic_on (\<lambda>x::(real^2)^'n. x) B"
    by (rule real_analytic_on_bounded_linear[OF Bo bounded_linear_ident])
  have pairB: "real_analytic_on (\<lambda>x::(real^2)^'n. (x, g x)) B"
    by (rule real_analytic_on_Pair[OF idB gana])
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
          (\<lambda>q::((real^2)^'n) \<times> (real^2).
             det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q))) (x, g x)) B"
    by (rule real_analytic_on_compose[OF pairB real_analytic_on_detHessU_dip subset_UNIV])
  thus ?thesis by simp
qed


section \<open>Layer 4b interface: the transversality witness, isolated\<close>

text \<open>\<^bold>\<open>The 4b interface.\<close>  The chart engine @{thm dip_critical_graph_dichotomy_unique}
  leaves a disjunction: on a chart \<open>B\<close> the moment-rank-drop locus along the critical
  graph is either ALL of \<open>B\<close> or thin.  The genuine remaining mathematics (the paper's
  Case-B appendix: branch decomposition over a good triple in \<open>c\<close>-adapted coordinates)
  is exactly the exclusion of the first alternative.  This theorem isolates that
  content as ONE hypothesis \<open>wit\<close> --- stated in the weakest form the engine can
  service: a witness point on each connected real-analytic critical chart through
  the bad basepoint on which the steered wavevector never vanishes --- and delivers
  the final chart interface consumed by the D3/D4 covering argument: a chart with
  uniqueness neighbourhood on which the bad \<open>x\<close>-locus is UNCONDITIONALLY thin
  (closure with empty interior).  \<open>wit\<close> plays the same role for 4b that \<open>nd\<close> plays
  in the two Robust3 sorries.\<close>

theorem dip_critical_chart_nowhere_dense:
  fixes x0 :: "(real^2)^'n::finite" and \<omega>b \<omega>0 \<omega>s :: "real^2"
  assumes crit: "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b = 0"
    and nds: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x0 \<omega>b) \<noteq> 0"
    and c0: "cvec_dip \<omega>0 \<omega>s \<omega>b \<noteq> 0"
    and wit: "\<And>B g. open B \<Longrightarrow> connected B \<Longrightarrow> x0 \<in> B \<Longrightarrow>
                real_analytic_on g B \<Longrightarrow> g x0 = \<omega>b \<Longrightarrow>
                (\<And>x. x \<in> B \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0) \<Longrightarrow>
                (\<And>x. x \<in> B \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0) \<Longrightarrow>
                (\<And>x. x \<in> B \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0) \<Longrightarrow>
                \<exists>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
  obtains B N g where
    "open B" and "connected B" and "x0 \<in> B"
    and "open N" and "(x0, \<omega>b) \<in> N"
    and "g x0 = \<omega>b" and "real_analytic_on g B"
    and "\<And>x. x \<in> B \<Longrightarrow>
           (x, g x) \<in> N \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
    and "\<And>x \<omega>. x \<in> B \<Longrightarrow> (x, \<omega>) \<in> N \<Longrightarrow>
           gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<Longrightarrow> \<omega> = g x"
    and "\<And>x. x \<in> B \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0"
    and "\<And>x. x \<in> B \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0"
    and "interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
proof -
  show ?thesis
  proof (rule dip_critical_graph_dichotomy_unique[OF crit nds])
    fix B0 N g
    assume B0o: "open B0" and B0c: "connected B0" and xB0: "x0 \<in> B0"
      and Nopen: "open N" and pN: "(x0, \<omega>b) \<in> N"
      and gx0: "g x0 = \<omega>b" and gana0: "real_analytic_on g B0"
      and graph0: "\<And>x. x \<in> B0 \<Longrightarrow>
             (x, g x) \<in> N \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
      and uniq0: "\<And>x \<omega>. x \<in> B0 \<Longrightarrow> (x, \<omega>) \<in> N \<Longrightarrow>
             gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0 \<Longrightarrow> \<omega> = g x"
      and dich0: "(\<forall>x\<in>B0. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0) \<or>
             interior (closure {x \<in> B0. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
    \<comment> \<open>shrink to a ball on which the steered wavevector along the graph is nonzero\<close>
    have cg_ana: "real_analytic_on (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) B0"
      by (rule real_analytic_on_compose[OF gana0 real_analytic_on_cvec_dip subset_UNIV])
    have cg_isC: "isCont (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) x" if "x \<in> B0" for x
      by (rule has_derivative_continuous[OF
            real_analytic_on_has_derivative_Dblinfun[OF cg_ana that]])
    have cg_cont: "continuous_on B0 (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x))"
      using cg_isC continuous_at_imp_continuous_on by blast
    have Sopen: "open (B0 \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) -` (- {0}))"
      by (rule continuous_open_preimage[OF cg_cont B0o])
         (rule open_Compl[OF closed_singleton])
    have dh_ana: "real_analytic_on
        (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) B0"
      by (rule real_analytic_on_detHessU_chart[OF B0o gana0])
    have dh_isC: "isCont (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) x"
      if "x \<in> B0" for x
      by (rule has_derivative_continuous[OF
            real_analytic_on_has_derivative_Dblinfun[OF dh_ana that]])
    have dh_cont: "continuous_on B0 (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)))"
      using dh_isC continuous_at_imp_continuous_on by blast
    have Dopen: "open (B0 \<inter> (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) -` (- {0}))"
      by (rule continuous_open_preimage[OF dh_cont B0o])
         (rule open_Compl[OF closed_singleton])
    have SDopen: "open ((B0 \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) -` (- {0}))
        \<inter> (B0 \<inter> (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) -` (- {0})))"
      by (rule open_Int[OF Sopen Dopen])
    have x0S: "x0 \<in> (B0 \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) -` (- {0}))
        \<inter> (B0 \<inter> (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) -` (- {0}))"
      using xB0 gx0 c0 nds by simp
    obtain \<epsilon> where e0: "0 < \<epsilon>"
      and esub: "ball x0 \<epsilon> \<subseteq> (B0 \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) -` (- {0}))
        \<inter> (B0 \<inter> (\<lambda>x. det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x))) -` (- {0}))"
      using openE[OF SDopen x0S] by blast
    define B where "B = ball x0 \<epsilon>"
    have Bo: "open B" by (simp add: B_def)
    have Bc: "connected B" by (simp add: B_def)
    have xB: "x0 \<in> B" by (simp add: B_def centre_in_ball e0)
    have Bsub: "B \<subseteq> B0" using esub by (auto simp: B_def)
    have cB: "cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0" if "x \<in> B" for x
      using esub that by (auto simp: B_def)
    have dB: "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0" if "x \<in> B" for x
      using esub that by (auto simp: B_def)
    have ganaB: "real_analytic_on g B"
      by (rule real_analytic_on_open_subset[OF gana0 Bo Bsub])
    have graphB: "(x, g x) \<in> N \<and> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
      if "x \<in> B" for x
      using graph0 Bsub that by blast
    have uniqB: "\<omega> = g x"
      if "x \<in> B" and "(x, \<omega>) \<in> N" and "gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> = 0"
      for x \<omega>
      using uniq0 Bsub that by blast
    \<comment> \<open>resolve the dichotomy: the witness kills the left disjunct\<close>
    have thin: "interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}) = {}"
    proof (cases rule: disjE[OF dich0])
      case 1
      have "\<exists>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
        by (rule wit[OF Bo Bc xB ganaB gx0]) (use graphB cB dB in blast)+
      with 1 Bsub show ?thesis by blast
    next
      case 2
      have "closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}
              \<subseteq> closure {x \<in> B0. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0}"
        using Bsub by (intro closure_mono) blast
      hence "interior (closure {x \<in> B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0})
              \<subseteq> interior (closure {x \<in> B0. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x = 0})"
        by (rule interior_mono)
      with 2 show ?thesis by blast
    qed
    show thesis
      by (rule that[OF Bo Bc xB Nopen pN gx0 ganaB graphB uniqB cB dB thin])
  qed
qed


section \<open>Layer 4b, step 2: the good-triple layer\<close>

text \<open>The Case-B branch certificates work in \<open>c\<close>-adapted coordinates over a GOOD
  TRIPLE: three elements whose \<open>c\<close>-parallel coordinates \<open>t_j = c \<bullet> p_j\<close> are pairwise
  distinct --- equivalently, \<open>c\<close> is orthogonal to no edge of the triple (the paper's
  \<open>B(T)\<close>-avoidance).  This theory provides:
  \<^enum> the goodness predicate and its \<open>t\<close>-separation reformulation;
  \<^enum> chart persistence: goodness at the basepoint of a critical chart survives on a
    shrunk ball (the same continuity-shrink the engine already uses);
  \<^enum> the two-triple cover criterion: if no edge of \<open>T\<^sub>1\<close> is parallel to an edge of
    \<open>T\<^sub>2\<close> (nine explicit \<open>2\<times>2\<close> determinants nonzero), then EVERY \<open>c \<noteq> 0\<close> is good
    for one of the two triples --- the pointwise form of the paper's
    \<open>lem:twotriplecover\<close>, and (via its failure being an explicit polynomial zero
    set) the future \<open>\<Xi>\<close>-certificate for the no-good-triple stratum.\<close>

subsection \<open>Goodness of a direction for a triple\<close>

definition triple_good :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "triple_good c p q r \<longleftrightarrow>
     c \<bullet> (p - q) \<noteq> 0 \<and> c \<bullet> (p - r) \<noteq> 0 \<and> c \<bullet> (q - r) \<noteq> 0"

lemma triple_good_t_distinct:
  "triple_good c p q r \<longleftrightarrow>
     c \<bullet> p \<noteq> c \<bullet> q \<and> c \<bullet> p \<noteq> c \<bullet> r \<and> c \<bullet> q \<noteq> c \<bullet> r"
  unfolding triple_good_def by (simp add: inner_diff_right)

text \<open>Goodness forces the three positions to be pairwise distinct.\<close>

lemma triple_good_distinct:
  assumes "triple_good c p q r"
  shows "p \<noteq> q" and "p \<noteq> r" and "q \<noteq> r"
  using assms unfolding triple_good_def by auto

subsection \<open>The edge determinant and the perpendicular characterisation\<close>

definition edge_det2 :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "edge_det2 a b = vec_nth a 1 * vec_nth b 2 - vec_nth a 2 * vec_nth b 1"

lemma common_perp_edge_det2:
  fixes c a b :: "real^2"
  assumes c0: "c \<noteq> 0" and pa: "c \<bullet> a = 0" and pb: "c \<bullet> b = 0"
  shows "edge_det2 a b = 0"
proof -
  have ca: "vec_nth c 1 * vec_nth a 1 + vec_nth c 2 * vec_nth a 2 = 0"
    using pa by (simp add: inner_vec_def sum_2)
  have cb: "vec_nth c 1 * vec_nth b 1 + vec_nth c 2 * vec_nth b 2 = 0"
    using pb by (simp add: inner_vec_def sum_2)
  have cnz: "vec_nth c 1 \<noteq> 0 \<or> vec_nth c 2 \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (vec_nth c 1 \<noteq> 0 \<or> vec_nth c 2 \<noteq> 0)"
    hence z: "vec_nth c 1 = 0" "vec_nth c 2 = 0" by auto
    have "vec_nth c m = 0" for m
      using exhaust_2[of m] z by auto
    hence "c = 0" by (simp add: Finite_Cartesian_Product.vec_eq_iff)
    with c0 show False by simp
  qed
  have key: "vec_nth c 1 * edge_det2 a b = 0 \<and> vec_nth c 2 * edge_det2 a b = 0"
  proof (rule conjI)
    have "vec_nth c 1 * edge_det2 a b
        = (vec_nth c 1 * vec_nth a 1 + vec_nth c 2 * vec_nth a 2) * vec_nth b 2
          - (vec_nth c 1 * vec_nth b 1 + vec_nth c 2 * vec_nth b 2) * vec_nth a 2"
      by (simp add: edge_det2_def algebra_simps)
    thus "vec_nth c 1 * edge_det2 a b = 0" by (simp add: ca cb)
  next
    have "vec_nth c 2 * edge_det2 a b
        = (vec_nth c 1 * vec_nth b 1 + vec_nth c 2 * vec_nth b 2) * vec_nth a 1
          - (vec_nth c 1 * vec_nth a 1 + vec_nth c 2 * vec_nth a 2) * vec_nth b 1"
      by (simp add: edge_det2_def algebra_simps)
    thus "vec_nth c 2 * edge_det2 a b = 0" by (simp add: ca cb)
  qed
  from cnz key show ?thesis by auto
qed

subsection \<open>The two-triple cover criterion\<close>

text \<open>If none of the nine cross edges of two triples are parallel (nine explicit
  \<open>2\<times>2\<close> determinants nonzero), every nonzero direction is good for at least one
  triple: a common bad direction would be perpendicular to an edge of each, forcing
  those two edges parallel.\<close>

definition triples_transverse :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> bool" where
  "triples_transverse p1 p2 p3 q1 q2 q3 \<longleftrightarrow>
     (\<forall>e1\<in>{p1 - p2, p1 - p3, p2 - p3}. \<forall>e2\<in>{q1 - q2, q1 - q3, q2 - q3}.
        edge_det2 e1 e2 \<noteq> 0)"

theorem two_triple_cover_pointwise:
  fixes c :: "real^2"
  assumes tt: "triples_transverse p1 p2 p3 q1 q2 q3"
    and c0: "c \<noteq> 0"
  shows "triple_good c p1 p2 p3 \<or> triple_good c q1 q2 q3"
proof (rule ccontr)
  assume "\<not> (triple_good c p1 p2 p3 \<or> triple_good c q1 q2 q3)"
  hence b1: "\<not> triple_good c p1 p2 p3" and b2: "\<not> triple_good c q1 q2 q3" by auto
  from b1 obtain e1 where e1: "e1 \<in> {p1 - p2, p1 - p3, p2 - p3}" and pe1: "c \<bullet> e1 = 0"
    unfolding triple_good_def by auto
  from b2 obtain e2 where e2: "e2 \<in> {q1 - q2, q1 - q3, q2 - q3}" and pe2: "c \<bullet> e2 = 0"
    unfolding triple_good_def by auto
  have "edge_det2 e1 e2 = 0"
    by (rule common_perp_edge_det2[OF c0 pe1 pe2])
  with tt e1 e2 show False
    unfolding triples_transverse_def by blast
qed

subsection \<open>Chart persistence of goodness\<close>

text \<open>Goodness of the steered wavevector for a triple of configuration elements,
  at the basepoint of a critical chart, persists on a shrunk ball: the three edge
  functionals \<open>x \<mapsto> cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (x $ i - x $ j)\<close> are real-analytic,
  hence continuous, and goodness is the preimage of three punctured lines.\<close>

lemma triple_good_chart_persist:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2" and x0 :: "(real^2)^'n"
    and i j k :: 'n
  assumes Bo: "open B" and xB: "x0 \<in> B"
    and gana: "real_analytic_on g B"
    and good0: "triple_good (cvec_dip \<omega>0 \<omega>s (g x0))
                  (vec_nth x0 i) (vec_nth x0 j) (vec_nth x0 k)"
  obtains B' where
    "open B'" and "connected B'" and "x0 \<in> B'" and "B' \<subseteq> B"
    and "\<And>x. x \<in> B' \<Longrightarrow>
           triple_good (cvec_dip \<omega>0 \<omega>s (g x)) (vec_nth x i) (vec_nth x j) (vec_nth x k)"
proof -
  have cg_ana: "real_analytic_on (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x)) B"
    by (rule real_analytic_on_compose[OF gana real_analytic_on_cvec_dip subset_UNIV])
  have nth_ana: "real_analytic_on (\<lambda>x::(real^2)^'n. vec_nth x m) B" for m
    by (rule real_analytic_on_bounded_linear[OF Bo bounded_linear_vec_nth])
  have edge_ana: "real_analytic_on
      (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x m - vec_nth x m')) B" for m m'
    by (intro real_analytic_on_inner[OF Bo cg_ana] real_analytic_on_diff nth_ana)
  have edge_cont: "continuous_on B
      (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x m - vec_nth x m'))" for m m'
  proof -
    have "isCont (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x m - vec_nth x m')) x"
      if "x \<in> B" for x
      by (rule has_derivative_continuous[OF
            real_analytic_on_has_derivative_Dblinfun[OF edge_ana that]])
    thus ?thesis using continuous_at_imp_continuous_on by blast
  qed
  define S where "S = B
      \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x i - vec_nth x j)) -` (- {0})
      \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x i - vec_nth x k)) -` (- {0})
      \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x j - vec_nth x k)) -` (- {0})"
  have S1: "open (B \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x i - vec_nth x j)) -` (- {0}))"
    by (rule continuous_open_preimage[OF edge_cont Bo])
       (rule open_Compl[OF closed_singleton])
  have S2: "open (B \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x i - vec_nth x k)) -` (- {0}))"
    by (rule continuous_open_preimage[OF edge_cont Bo])
       (rule open_Compl[OF closed_singleton])
  have S3: "open (B \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x j - vec_nth x k)) -` (- {0}))"
    by (rule continuous_open_preimage[OF edge_cont Bo])
       (rule open_Compl[OF closed_singleton])
  have S_eq: "S = (B \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x i - vec_nth x j)) -` (- {0}))
      \<inter> ((B \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x i - vec_nth x k)) -` (- {0}))
      \<inter> (B \<inter> (\<lambda>x. cvec_dip \<omega>0 \<omega>s (g x) \<bullet> (vec_nth x j - vec_nth x k)) -` (- {0})))"
    unfolding S_def by auto
  have Sopen: "open S"
    unfolding S_eq by (intro open_Int S1 S2 S3)
  have x0S: "x0 \<in> S"
    using xB good0 unfolding S_def triple_good_def by simp
  obtain \<epsilon> where e0: "0 < \<epsilon>" and esub: "ball x0 \<epsilon> \<subseteq> S"
    using openE[OF Sopen x0S] by blast
  have bo: "open (ball x0 \<epsilon>)" by simp
  have bc: "connected (ball x0 \<epsilon>)" by simp
  have bx: "x0 \<in> ball x0 \<epsilon>" by (simp add: centre_in_ball e0)
  have bsub: "ball x0 \<epsilon> \<subseteq> B" using esub by (auto simp: S_def)
  have bgood: "triple_good (cvec_dip \<omega>0 \<omega>s (g x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)"
    if "x \<in> ball x0 \<epsilon>" for x
    using esub that unfolding S_def triple_good_def by auto
  show ?thesis
    by (rule that[OF bo bc bx bsub bgood])
qed


section \<open>Layer 4b, step 1: the concrete c-adapted transport matrix\<close>

text \<open>For \<open>c \<noteq> 0\<close>, the matrix \<open>cadapt c\<close> (columns \<open>c/|c|\<^sup>2\<close> and \<open>c\<^sup>\<perp>\<close>) satisfies the
  transport convention of the \<open>applyT\<close> moment laws, \<open>transpose T *v c = c0_paper\<close>,
  with \<open>det = 1\<close>: the entry point of the c-adapted coordinate layer for the Case-B
  branch certificates.\<close>

definition cadapt :: "real^2 \<Rightarrow> real^2^2" where
  "cadapt c = vector
     [ vector [vec_nth c 1 / (norm c)\<^sup>2, - vec_nth c 2],
       vector [vec_nth c 2 / (norm c)\<^sup>2,   vec_nth c 1] ]"

lemma norm2_sum_sq: "(norm (c::real^2))\<^sup>2 = vec_nth c 1 * vec_nth c 1 + vec_nth c 2 * vec_nth c 2"
  by (simp add: power2_norm_eq_inner inner_vec_def sum_2)

lemma norm2_nz:
  assumes "c \<noteq> (0::real^2)"
  shows "(norm c)\<^sup>2 \<noteq> 0"
  using assms by simp

lemma cadapt_transport:
  assumes c0: "c \<noteq> (0::real^2)"
  shows "transpose (cadapt c) *v c = c0_paper"
proof -
  have n2: "vec_nth c 1 * vec_nth c 1 + vec_nth c 2 * vec_nth c 2 \<noteq> 0"
    using norm2_nz[OF c0] by (simp add: norm2_sum_sq)
  have comp: "vec_nth (transpose (cadapt c) *v c) m = vec_nth c0_paper m" for m
    using exhaust_2[of m] n2
    by (elim disjE)
       (simp_all add: cadapt_def c0_paper_def transpose_def matrix_vector_mult_def
          sum_2 norm2_sum_sq add_divide_distrib [symmetric])
  show ?thesis
    using comp by (simp add: Finite_Cartesian_Product.vec_eq_iff)
qed

lemma cadapt_det:
  assumes c0: "c \<noteq> (0::real^2)"
  shows "det (cadapt c) = 1"
proof -
  have n2: "vec_nth c 1 * vec_nth c 1 + vec_nth c 2 * vec_nth c 2 \<noteq> 0"
    using norm2_nz[OF c0] by (simp add: norm2_sum_sq)
  have "det (cadapt c)
      = vec_nth (vec_nth (cadapt c) 1) 1 * vec_nth (vec_nth (cadapt c) 2) 2
        - vec_nth (vec_nth (cadapt c) 1) 2 * vec_nth (vec_nth (cadapt c) 2) 1"
    by (rule det_2)
  also have "\<dots> = (vec_nth c 1 * vec_nth c 1 + vec_nth c 2 * vec_nth c 2) / (norm c)\<^sup>2"
    by (simp add: cadapt_def add_divide_distrib field_simps)
  also have "\<dots> = 1"
    using n2 by (simp add: norm2_sum_sq)
  finally show ?thesis .
qed

lemma cadapt_invertible:
  assumes "c \<noteq> (0::real^2)"
  shows "invertible (cadapt c)"
  by (simp add: invertible_det_nz cadapt_det[OF assms])


section \<open>Layer 4b, step 1 (cont.): the transport laws migrated into bridge scope\<close>

text \<open>Verbatim migration of the \<open>applyT\<close> transport bricks from the top of
  \<open>Nonemptiness_Robust3\<close> (L5--155, L322--341) into the bridge: \<open>M12_moment_applyT\<close>,
  \<open>M_paper_applyT\<close>, \<open>applyT_linear\<close>, \<open>applyT_surj\<close>.  Together with the layer-1
  \<open>cadapt\<close> witness matrix these complete the c-adapted transport entry point for the
  Case-B branch certificates.  When Robust3 is rewired to import the bridge (layer 5),
  its local copies are to be DELETED.\<close>

lemma M12_moment_applyT:
  fixes T :: "real^2^2"
  assumes "transpose T *v c = c0_paper"
  shows "M12_moment (applyT T y) c
       = of_real ((vec_nth (vec_nth T 1) 1) * (vec_nth (vec_nth T 2) 1)) * M11_moment y c0_paper
       + of_real ((vec_nth (vec_nth T 1) 1) * (vec_nth (vec_nth T 2) 2) + (vec_nth (vec_nth T 1) 2) * (vec_nth (vec_nth T 2) 1)) * M12_moment y c0_paper
       + of_real ((vec_nth (vec_nth T 1) 2) * (vec_nth (vec_nth T 2) 2)) * M22_moment y c0_paper"
proof -
  \<comment> \<open>Abbreviate the four matrix entries as scalars: the pointwise \<open>key\<close>
      identity otherwise carries ~24 vec-nth occurrences and hangs elaboration
      at parse time (the *-overload graph noted at \<^const>\<open>w_M12\<close>).  With the
      entries named, it parses immediately.\<close>
  define t11 where "t11 = vec_nth (vec_nth T 1) 1"
  define t12 where "t12 = vec_nth (vec_nth T 1) 2"
  define t21 where "t21 = vec_nth (vec_nth T 2) 1"
  define t22 where "t22 = vec_nth (vec_nth T 2) 2"
  have key: "\<And>n.
       phase c (applyT T y) n * of_real (w_M12 (vec_nth (applyT T y) n))
       =
       phase c0_paper y n
         * (of_real ((vec_nth (vec_nth y n) 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
         * (of_real (w_M12 (vec_nth y n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
         * (of_real ((vec_nth (vec_nth y n) 2)\<^sup>2) * of_real (t12 * t22))"
  proof -
    fix n
    have ph: "phase c (applyT T y) n = phase c0_paper y n"
      by (rule phase_applyT[OF assms])
    have lin1: "vec_nth (vec_nth (applyT T y) n) 1 = t11 * vec_nth (vec_nth y n) 1 + t12 * vec_nth (vec_nth y n) 2"
      unfolding t11_def t12_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    have lin2: "vec_nth (vec_nth (applyT T y) n) 2 = t21 * vec_nth (vec_nth y n) 1 + t22 * vec_nth (vec_nth y n) 2"
      unfolding t21_def t22_def
      by (simp add: applyT_def matrix_vector_mult_def sum_2)
    show "phase c (applyT T y) n * of_real (w_M12 (vec_nth (applyT T y) n))
       =
       phase c0_paper y n
         * (of_real ((vec_nth (vec_nth y n) 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
         * (of_real (w_M12 (vec_nth y n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
         * (of_real ((vec_nth (vec_nth y n) 2)\<^sup>2) * of_real (t12 * t22))"
      using ph lin1 lin2
      by (simp add: w_M12_def of_real_add of_real_mult power2_eq_square algebra_simps)
  qed

  have sum_key:
    "(\<Sum>n\<in>UNIV. phase c (applyT T y) n * of_real (w_M12 (vec_nth (applyT T y) n)))
     =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real ((vec_nth (vec_nth y n) 1)\<^sup>2) * of_real (t11 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (vec_nth y n)) * of_real (t11 * t22 + t12 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real ((vec_nth (vec_nth y n) 2)\<^sup>2) * of_real (t12 * t22)))"
  proof -
    have "(\<Sum>n\<in>UNIV. phase c (applyT T y) n * of_real (w_M12 (vec_nth (applyT T y) n)))
       =
      (\<Sum>n\<in>UNIV.
         phase c0_paper y n
           * (of_real ((vec_nth (vec_nth y n) 1)\<^sup>2) * of_real (t11 * t21))
       + phase c0_paper y n
           * (of_real (w_M12 (vec_nth y n)) * of_real (t11 * t22 + t12 * t21))
       + phase c0_paper y n
           * (of_real ((vec_nth (vec_nth y n) 2)\<^sup>2) * of_real (t12 * t22)))"
      by (rule sum.cong, rule refl, simp add: key)
    also have "\<dots> =
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real ((vec_nth (vec_nth y n) 1)\<^sup>2) * of_real (t11 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real (w_M12 (vec_nth y n)) * of_real (t11 * t22 + t12 * t21)))
     +
     (\<Sum>n\<in>UNIV. phase c0_paper y n
          * (of_real ((vec_nth (vec_nth y n) 2)\<^sup>2) * of_real (t12 * t22)))"
      by (simp add: sum.distrib add.assoc)
    finally show ?thesis .
  qed

  show ?thesis
      unfolding M11_moment_def M12_moment_def M22_moment_def
      using sum_key[unfolded t11_def t12_def t21_def t22_def]
      by (simp add: sum_distrib_left algebra_simps power2_eq_square ac_simps)
qed


text \<open>\<^bold>\<open>[E] brick 4a: the vector moment law.\<close>  Bundling the six \<open>*_moment_applyT\<close>
  laws into one equation \<open>M_paper(applyT T y) c = L\<^sub>T (M_paper y c\<^sub>0)\<close>.  The four matrix
  entries are named \<open>a,b,p,q\<close> via \<^theory_text>\<open>defines\<close> so the explicit transported vector parses
  (a bare \<open>T$i$j\<close> form would carry ~16 vec-nth occurrences and hang elaboration).\<close>


lemma M_paper_applyT:
  fixes T :: "real^2^2" and a b p q :: real
  assumes Tc: "transpose T *v c = c0_paper"
  defines "a \<equiv> vec_nth (vec_nth T 1) 1" and "b \<equiv> vec_nth (vec_nth T 1) 2"
      and "p \<equiv> vec_nth (vec_nth T 2) 1" and "q \<equiv> vec_nth (vec_nth T 2) 2"
  shows "M_paper (applyT T y) c = vector
    [ A_moment y c0_paper,
      of_real a * M1_moment y c0_paper + of_real b * M2_moment y c0_paper,
      of_real p * M1_moment y c0_paper + of_real q * M2_moment y c0_paper,
      of_real (a\<^sup>2) * M11_moment y c0_paper
        + of_real (2 * a * b) * M12_moment y c0_paper
        + of_real (b\<^sup>2) * M22_moment y c0_paper,
      of_real (a * p) * M11_moment y c0_paper
        + of_real (a * q + b * p) * M12_moment y c0_paper
        + of_real (b * q) * M22_moment y c0_paper,
      of_real (p\<^sup>2) * M11_moment y c0_paper
        + of_real (2 * p * q) * M12_moment y c0_paper
        + of_real (q\<^sup>2) * M22_moment y c0_paper ]"
proof (subst Finite_Cartesian_Product.vec_eq_iff, intro allI)
  fix i :: 6
  consider "i = 1" | "i = 2" | "i = 3" | "i = 4" | "i = 5" | "i = 6"
    using exhaust_6[of i] by blast
  then show "vec_nth (M_paper (applyT T y) c) i =
      vec_nth (vector
        [ A_moment y c0_paper,
          of_real a * M1_moment y c0_paper + of_real b * M2_moment y c0_paper,
          of_real p * M1_moment y c0_paper + of_real q * M2_moment y c0_paper,
          of_real (a\<^sup>2) * M11_moment y c0_paper
            + of_real (2 * a * b) * M12_moment y c0_paper
            + of_real (b\<^sup>2) * M22_moment y c0_paper,
          of_real (a * p) * M11_moment y c0_paper
            + of_real (a * q + b * p) * M12_moment y c0_paper
            + of_real (b * q) * M22_moment y c0_paper,
          of_real (p\<^sup>2) * M11_moment y c0_paper
            + of_real (2 * p * q) * M12_moment y c0_paper
            + of_real (q\<^sup>2) * M22_moment y c0_paper ]) i"
  proof cases
    case 1 then show ?thesis
      by (simp add: A_moment_applyT[OF Tc] vector_def)
  next
    case 2 then show ?thesis
      unfolding a_def b_def by (simp add: M1_moment_applyT[OF Tc] vector_def)
  next
    case 3 then show ?thesis
      unfolding p_def q_def by (simp add: M2_moment_applyT[OF Tc] vector_def)
  next
    case 4 then show ?thesis
      unfolding a_def b_def by (simp add: M11_moment_applyT[OF Tc] vector_def)
  next
    case 5 then show ?thesis
      unfolding a_def b_def p_def q_def
      by (simp add: M12_moment_applyT[OF Tc] vector_def)
  next
    case 6 then show ?thesis
      unfolding p_def q_def by (simp add: M22_moment_applyT[OF Tc] vector_def)
  qed
qed

lemma applyT_linear: "linear (applyT T)"
proof (rule linearI)
  have l: "linear ((*v) T)" by (rule matrix_vector_mul_linear)
  show "applyT T (x + y) = applyT T x + applyT T y" for x y :: "(real^2)^'n"
    by (simp add: applyT_def Finite_Cartesian_Product.vec_eq_iff vector_add_component linear_add[OF l])
  show "applyT T (r *\<^sub>R x) = r *\<^sub>R applyT T x" for r and x :: "(real^2)^'n"
    by (simp add: applyT_def Finite_Cartesian_Product.vec_eq_iff vector_scaleR_component linear_cmul[OF l])
qed

lemma applyT_surj:
  assumes "invertible T" shows "surj (applyT T :: (real^2)^'n \<Rightarrow> _)"
proof -
  obtain B :: "real^2^2" where B: "T ** B = mat 1"
    using assms unfolding invertible_def by blast
  have "applyT T (applyT B z) = z" for z :: "(real^2)^'n"
    by (simp add: applyT_def Finite_Cartesian_Product.vec_eq_iff matrix_vector_mul_assoc B matrix_vector_mul_lid)
  thus ?thesis by (metis surjI)
qed


section \<open>Layer 4b, step 3: division closure and the Case-B cofactor primitives\<close>

text \<open>Two ingredients for the branch certificates:
  \<^enum> the missing DIVISION closure for the analytic kit (\<open>inverse\<close>/\<open>divide\<close> where the
    denominator is nonvanishing) --- needed for the gauge quantities of the branches
    (e.g. \<open>G\<^sub>2\<^sub>2 = H\<^sub>1\<^sub>1 - H\<^sub>1\<^sub>2\<^sup>2/H\<^sub>2\<^sub>2\<close>);
  \<^enum> the three familiar cofactors \<open>K, L, M\<close> of the Case-B appendix (tex 3650), in
    \<open>\<kappa>\<close>-SCALED form: with \<open>t_j = c \<bullet> p_j\<close> (\<open>= \<kappa> u_j\<close>) and \<open>w_j = edge_det2 c p_j\<close>
    (\<open>= \<kappa> v_j\<close>) the scaled columns are polynomial-trigonometric in \<open>(c, p)\<close>, so the
    cofactors are ENTIRE jointly --- no division, no square roots.  The scaled and
    paper cofactors differ by explicit positive powers of \<open>\<kappa> = |c|\<close> per row, so all
    nonvanishing certificates transfer; the exact \<open>\<kappa>\<close>-bookkeeping enters only when
    the \<open>v\<close>-block Jacobian identity (\<open>prop:vblock\<close>) is derived in step 4.\<close>

subsection \<open>Division closure for the analytic kit\<close>

lemma has_holo_extension_at_inverse:
  fixes c :: real
  assumes c0: "c \<noteq> 0"
  shows "has_holo_extension_at (\<lambda>t. inverse t) c"
proof -
  have holo: "(\<lambda>z::complex. inverse z) holomorphic_on ball (complex_of_real c) \<bar>c\<bar>"
  proof (intro holomorphic_intros)
    fix z assume "z \<in> ball (complex_of_real c) \<bar>c\<bar>"
    hence "dist z (complex_of_real c) < \<bar>c\<bar>" by (simp add: dist_commute)
    moreover have "dist 0 (complex_of_real c) = \<bar>c\<bar>" by simp
    ultimately show "z \<noteq> 0" by auto
  qed
  have agree: "\<forall>x. \<bar>x - c\<bar> < \<bar>c\<bar> \<longrightarrow>
      inverse (complex_of_real x) = complex_of_real (inverse x)"
    by (simp add: of_real_inverse)
  have "\<exists>g. g holomorphic_on ball (complex_of_real c) \<bar>c\<bar>
          \<and> (\<forall>x. \<bar>x - c\<bar> < \<bar>c\<bar> \<longrightarrow> g (complex_of_real x) = complex_of_real (inverse x))"
    using holo agree by blast
  thus ?thesis
    unfolding has_holo_extension_at_def
    by (intro exI[of _ "\<bar>c\<bar>"]) (simp add: c0)
qed

lemma real_analytic_on_inverse_1d:
  "real_analytic_on (\<lambda>t::real. inverse t) (- {0})"
  unfolding real_analytic_on_1d_iff
  by (auto simp: real_analytic_at_1d_iff_holo_extension
      intro: has_holo_extension_at_inverse)

lemma real_analytic_on_inverse_comp:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes F: "real_analytic_on f U"
    and nz: "\<And>x. x \<in> U \<Longrightarrow> f x \<noteq> 0"
  shows "real_analytic_on (\<lambda>x. inverse (f x)) U"
proof -
  have img: "f ` U \<subseteq> - {0}" using nz by auto
  show ?thesis
    by (rule real_analytic_on_compose[OF F real_analytic_on_inverse_1d img])
qed

lemma real_analytic_on_divide:
  fixes f g :: "'a::euclidean_space \<Rightarrow> real"
  assumes F: "real_analytic_on f U" and G: "real_analytic_on g U"
    and nz: "\<And>x. x \<in> U \<Longrightarrow> g x \<noteq> 0"
  shows "real_analytic_on (\<lambda>x. f x / g x) U"
proof -
  have "real_analytic_on (\<lambda>x. f x * inverse (g x)) U"
    by (intro real_analytic_on_mult F real_analytic_on_inverse_comp[OF G nz])
  thus ?thesis by (simp add: field_simps)
qed

subsection \<open>The explicit \<open>3\<times>3\<close> determinant primitive\<close>

definition det3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "det3 a1 a2 a3 b1 b2 b3 e1 e2 e3 =
     a1 * (b2 * e3 - b3 * e2) - a2 * (b1 * e3 - b3 * e1) + a3 * (b1 * e2 - b2 * e1)"

lemma real_analytic_on_det3:
  fixes A1 A2 A3 B1 B2 B3 E1 E2 E3 :: "'a::euclidean_space \<Rightarrow> real"
  assumes U: "open U"
    and "real_analytic_on A1 U" "real_analytic_on A2 U" "real_analytic_on A3 U"
    and "real_analytic_on B1 U" "real_analytic_on B2 U" "real_analytic_on B3 U"
    and "real_analytic_on E1 U" "real_analytic_on E2 U" "real_analytic_on E3 U"
  shows "real_analytic_on (\<lambda>q. det3 (A1 q) (A2 q) (A3 q)
                                    (B1 q) (B2 q) (B3 q)
                                    (E1 q) (E2 q) (E3 q)) U"
  unfolding det3_def
  by (intro real_analytic_on_add real_analytic_on_diff real_analytic_on_mult assms)

subsection \<open>The c-adapted triple scalars\<close>

text \<open>\<open>tcoord c p = c \<bullet> p\<close> is the paper's \<open>t_j = \<kappa> u_j\<close>; \<open>wcoord c p = edge_det2 c p\<close>
  is \<open>\<kappa> v_j\<close> (the \<open>c\<^sup>\<perp>\<close>-coordinate scaled by \<open>\<kappa>\<close>).\<close>

definition tcoord :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "tcoord c p = c \<bullet> p"

definition wcoord :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "wcoord c p = edge_det2 c p"

lemma real_analytic_on_tcoord:
  fixes C P :: "'a::euclidean_space \<Rightarrow> real^2"
  assumes U: "open U" and C: "real_analytic_on C U" and P: "real_analytic_on P U"
  shows "real_analytic_on (\<lambda>q. tcoord (C q) (P q)) U"
  unfolding tcoord_def by (rule real_analytic_on_inner[OF U C P])

lemma real_analytic_on_wcoord:
  fixes C P :: "'a::euclidean_space \<Rightarrow> real^2"
  assumes U: "open U" and C: "real_analytic_on C U" and P: "real_analytic_on P U"
  shows "real_analytic_on (\<lambda>q. wcoord (C q) (P q)) U"
proof -
  have comp: "real_analytic_on (\<lambda>q. vec_nth (F q) m) U"
    if "real_analytic_on F U" for F :: "'a \<Rightarrow> real^2" and m
  proof -
    have "real_analytic_on (\<lambda>q. F q \<bullet> axis m 1) U"
      by (rule real_analytic_on_inner_component[OF that])
    moreover have "(\<lambda>q. F q \<bullet> axis m 1) = (\<lambda>q. vec_nth (F q) m)"
      by (rule ext) (simp add: inner_axis)
    ultimately show ?thesis by simp
  qed
  show ?thesis
    unfolding wcoord_def edge_det2_def
    by (intro real_analytic_on_diff real_analytic_on_mult comp C P)
qed

subsection \<open>The three familiar cofactors (\<open>\<kappa>\<close>-scaled)\<close>

text \<open>Rows follow tex 3650 with \<open>u_j c_j \<rightarrow> t_j cos t_j\<close> and \<open>v_j c_j \<rightarrow> w_j cos t_j\<close>
  (each substitution scales a row by \<open>\<kappa> > 0\<close>): \<open>cofK = \<kappa>\<^sup>2 K\<close>, \<open>cofL = \<kappa> L\<close>,
  \<open>cofM = \<kappa> M\<close>.\<close>

definition cofK :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "cofK c p1 p2 p3 = det3
     (sin (tcoord c p1)) (sin (tcoord c p2)) (sin (tcoord c p3))
     (tcoord c p1 * cos (tcoord c p1)) (tcoord c p2 * cos (tcoord c p2))
       (tcoord c p3 * cos (tcoord c p3))
     (wcoord c p1 * cos (tcoord c p1)) (wcoord c p2 * cos (tcoord c p2))
       (wcoord c p3 * cos (tcoord c p3))"

definition cofL :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "cofL c p1 p2 p3 = det3
     (cos (tcoord c p1)) (cos (tcoord c p2)) (cos (tcoord c p3))
     (sin (tcoord c p1)) (sin (tcoord c p2)) (sin (tcoord c p3))
     (wcoord c p1 * cos (tcoord c p1)) (wcoord c p2 * cos (tcoord c p2))
       (wcoord c p3 * cos (tcoord c p3))"

definition cofM :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "cofM c p1 p2 p3 = det3
     (cos (tcoord c p1)) (cos (tcoord c p2)) (cos (tcoord c p3))
     (sin (tcoord c p1)) (sin (tcoord c p2)) (sin (tcoord c p3))
     (tcoord c p1 * cos (tcoord c p1)) (tcoord c p2 * cos (tcoord c p2))
       (tcoord c p3 * cos (tcoord c p3))"

lemma real_analytic_on_cofK:
  fixes C P1 P2 P3 :: "'a::euclidean_space \<Rightarrow> real^2"
  assumes U: "open U" and C: "real_analytic_on C U"
    and P1: "real_analytic_on P1 U" and P2: "real_analytic_on P2 U"
    and P3: "real_analytic_on P3 U"
  shows "real_analytic_on (\<lambda>q. cofK (C q) (P1 q) (P2 q) (P3 q)) U"
  unfolding cofK_def
  by (intro real_analytic_on_det3[OF U] real_analytic_on_mult
        real_analytic_on_sin_comp real_analytic_on_cos_comp
        real_analytic_on_tcoord[OF U C] real_analytic_on_wcoord[OF U C] P1 P2 P3)

lemma real_analytic_on_cofL:
  fixes C P1 P2 P3 :: "'a::euclidean_space \<Rightarrow> real^2"
  assumes U: "open U" and C: "real_analytic_on C U"
    and P1: "real_analytic_on P1 U" and P2: "real_analytic_on P2 U"
    and P3: "real_analytic_on P3 U"
  shows "real_analytic_on (\<lambda>q. cofL (C q) (P1 q) (P2 q) (P3 q)) U"
  unfolding cofL_def
  by (intro real_analytic_on_det3[OF U] real_analytic_on_mult
        real_analytic_on_sin_comp real_analytic_on_cos_comp
        real_analytic_on_tcoord[OF U C] real_analytic_on_wcoord[OF U C] P1 P2 P3)

lemma real_analytic_on_cofM:
  fixes C P1 P2 P3 :: "'a::euclidean_space \<Rightarrow> real^2"
  assumes U: "open U" and C: "real_analytic_on C U"
    and P1: "real_analytic_on P1 U" and P2: "real_analytic_on P2 U"
    and P3: "real_analytic_on P3 U"
  shows "real_analytic_on (\<lambda>q. cofM (C q) (P1 q) (P2 q) (P3 q)) U"
  unfolding cofM_def
  by (intro real_analytic_on_det3[OF U] real_analytic_on_mult
        real_analytic_on_sin_comp real_analytic_on_cos_comp
        real_analytic_on_tcoord[OF U C] real_analytic_on_wcoord[OF U C] P1 P2 P3)

text \<open>The chart-composed forms actually consumed by the certificates: along a critical
  graph, each cofactor of a fixed triple of elements is real-analytic in \<open>x\<close>.\<close>

lemma real_analytic_on_cofK_chart:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2" and i j k :: 'n
  assumes Bo: "open B" and gana: "real_analytic_on g B"
  shows "real_analytic_on (\<lambda>x. cofK (cvec_dip \<omega>0 \<omega>s (g x))
           (vec_nth x i) (vec_nth x j) (vec_nth x k)) B"
  by (intro real_analytic_on_cofK[OF Bo
        real_analytic_on_compose[OF gana real_analytic_on_cvec_dip subset_UNIV]]
      real_analytic_on_bounded_linear[OF Bo bounded_linear_vec_nth])

lemma real_analytic_on_cofL_chart:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2" and i j k :: 'n
  assumes Bo: "open B" and gana: "real_analytic_on g B"
  shows "real_analytic_on (\<lambda>x. cofL (cvec_dip \<omega>0 \<omega>s (g x))
           (vec_nth x i) (vec_nth x j) (vec_nth x k)) B"
  by (intro real_analytic_on_cofL[OF Bo
        real_analytic_on_compose[OF gana real_analytic_on_cvec_dip subset_UNIV]]
      real_analytic_on_bounded_linear[OF Bo bounded_linear_vec_nth])

lemma real_analytic_on_cofM_chart:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2" and i j k :: 'n
  assumes Bo: "open B" and gana: "real_analytic_on g B"
  shows "real_analytic_on (\<lambda>x. cofM (cvec_dip \<omega>0 \<omega>s (g x))
           (vec_nth x i) (vec_nth x j) (vec_nth x k)) B"
  by (intro real_analytic_on_cofM[OF Bo
        real_analytic_on_compose[OF gana real_analytic_on_cvec_dip subset_UNIV]]
      real_analytic_on_bounded_linear[OF Bo bounded_linear_vec_nth])


section \<open>Layer 4b, step 5 (pre-assembled): reduction of \<open>wit\<close> to the branch core\<close>

text \<open>This theory closes everything around the Case-B branch computations.  Contents:
  \<^enum> an EXPLICIT configuration whose two designated triples are transverse (all nine
    cross-edge determinants nonzero) --- so the transversality product, a polynomial
    in \<open>x\<close> alone (no \<open>c\<close>!), is globally nontrivial;
  \<^enum> hence EVERY nonempty open set of configurations contains a transverse point
    (the workhorse on the product certificate --- no Baire, and no global
    perturbation: this REPLACES the paper's global two-triple neighbourhood \<open>V\<close>);
  \<^enum> \<open>dip_wit_reduction\<close>: the witness obligation \<open>wit\<close> of
    @{thm dip_critical_chart_nowhere_dense} follows from ONE remaining hypothesis
    \<open>wit_core\<close> --- a witness on any connected analytic critical chart carrying a
    FIXED good triple.  \<open>wit_core\<close> is exactly what the four Case-B branch
    corollaries (tex \<open>cor:vpair22-full\<close>, \<open>cor:uphi-exhausted\<close>, \<open>cor:Lambda-closed\<close>,
    \<open>cor:H11-closed\<close>) prove; it is the ONLY remaining 4b obligation.\<close>

subsection \<open>An explicit transverse configuration\<close>

lemma triples_transverse_witness:
  fixes \<iota> :: "6 \<Rightarrow> 'n::finite"
  assumes inji: "inj \<iota>"
  shows "\<exists>x::(real^2)^'n. triples_transverse
           (vec_nth x (\<iota> 1)) (vec_nth x (\<iota> 2)) (vec_nth x (\<iota> 3))
           (vec_nth x (\<iota> 4)) (vec_nth x (\<iota> 5)) (vec_nth x (\<iota> 6))"
proof -
  define x :: "(real^2)^'n" where
    "x = (\<chi> m. if m = \<iota> 1 then vector [0, 0]
          else if m = \<iota> 2 then vector [1, 0]
          else if m = \<iota> 3 then vector [0, 1]
          else if m = \<iota> 4 then vector [0, 0]
          else if m = \<iota> 5 then vector [1, 2]
          else if m = \<iota> 6 then vector [3, 1]
          else 0)"
  have ne: "(\<iota> a = \<iota> b) = (a = b)" for a b
    by (rule inj_eq[OF inji])
  have P1: "vec_nth x (\<iota> 1) = vector [0, 0]"
    by (simp add: x_def ne)
  have P2: "vec_nth x (\<iota> 2) = vector [1, 0]"
    by (simp add: x_def ne)
  have P3: "vec_nth x (\<iota> 3) = vector [0, 1]"
    by (simp add: x_def ne)
  have P4: "vec_nth x (\<iota> 4) = vector [0, 0]"
    by (simp add: x_def ne)
  have P5: "vec_nth x (\<iota> 5) = vector [1, 2]"
    by (simp add: x_def ne)
  have P6: "vec_nth x (\<iota> 6) = vector [3, 1]"
    by (simp add: x_def ne)
  have "triples_transverse
           (vec_nth x (\<iota> 1)) (vec_nth x (\<iota> 2)) (vec_nth x (\<iota> 3))
           (vec_nth x (\<iota> 4)) (vec_nth x (\<iota> 5)) (vec_nth x (\<iota> 6))"
    unfolding triples_transverse_def edge_det2_def
    by (simp add: P1 P2 P3 P4 P5 P6 vector_minus_component)
  thus ?thesis by blast
qed

subsection \<open>The transversality product certificate\<close>

text \<open>The product of the nine cross-edge determinants, written as an EXPLICIT
  nine-factor product (index-based, so it is a polynomial in \<open>x\<close> and in particular
  jointly real-analytic --- a set-based product would not be, since coincidences
  collapse the set).\<close>

definition edet :: "(6 \<Rightarrow> 'n::finite) \<Rightarrow> (real^2)^'n \<Rightarrow> 6 \<Rightarrow> 6 \<Rightarrow> 6 \<Rightarrow> 6 \<Rightarrow> real" where
  "edet \<iota> x a b c d = edge_det2 (vec_nth x (\<iota> a) - vec_nth x (\<iota> b))
                                (vec_nth x (\<iota> c) - vec_nth x (\<iota> d))"

definition ttprod :: "(6 \<Rightarrow> 'n::finite) \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "ttprod \<iota> x =
     edet \<iota> x 1 2 4 5 * edet \<iota> x 1 2 4 6 * edet \<iota> x 1 2 5 6
   * edet \<iota> x 1 3 4 5 * edet \<iota> x 1 3 4 6 * edet \<iota> x 1 3 5 6
   * edet \<iota> x 2 3 4 5 * edet \<iota> x 2 3 4 6 * edet \<iota> x 2 3 5 6"

lemma ttprod_nz_iff:
  "ttprod \<iota> x \<noteq> 0 \<longleftrightarrow> triples_transverse
     (vec_nth x (\<iota> 1)) (vec_nth x (\<iota> 2)) (vec_nth x (\<iota> 3))
     (vec_nth x (\<iota> 4)) (vec_nth x (\<iota> 5)) (vec_nth x (\<iota> 6))"
  unfolding ttprod_def edet_def triples_transverse_def
  by auto

lemma real_analytic_on_ttprod:
  fixes \<iota> :: "6 \<Rightarrow> 'n::finite"
  shows "real_analytic_on (ttprod \<iota>) UNIV"
proof -
  have nth2: "real_analytic_on (\<lambda>x::(real^2)^'n. vec_nth (vec_nth x m) k) UNIV" for m k
    by (rule real_analytic_on_bounded_linear[OF open_UNIV
          bounded_linear_compose[OF bounded_linear_vec_nth bounded_linear_vec_nth]])
  have ed: "real_analytic_on (\<lambda>x::(real^2)^'n. edet \<iota> x a b c d) UNIV" for a b c d
  proof -
    have expand: "(\<lambda>x::(real^2)^'n. edet \<iota> x a b c d)
        = (\<lambda>x. (vec_nth (vec_nth x (\<iota> a)) 1 - vec_nth (vec_nth x (\<iota> b)) 1)
             * (vec_nth (vec_nth x (\<iota> c)) 2 - vec_nth (vec_nth x (\<iota> d)) 2)
             - (vec_nth (vec_nth x (\<iota> a)) 2 - vec_nth (vec_nth x (\<iota> b)) 2)
             * (vec_nth (vec_nth x (\<iota> c)) 1 - vec_nth (vec_nth x (\<iota> d)) 1))"
      by (rule ext) (simp add: edet_def edge_det2_def vector_minus_component)
    show ?thesis
      unfolding expand
      by (intro real_analytic_on_diff real_analytic_on_mult nth2)
  qed
  show ?thesis
    unfolding ttprod_def[abs_def]
    by (intro real_analytic_on_mult ed)
qed

lemma transverse_point_in_open:
  fixes \<iota> :: "6 \<Rightarrow> 'n::finite" and B :: "((real^2)^'n) set"
  assumes inji: "inj \<iota>" and Bo: "open B" and Bne: "B \<noteq> {}"
  shows "\<exists>x\<in>B. triples_transverse
           (vec_nth x (\<iota> 1)) (vec_nth x (\<iota> 2)) (vec_nth x (\<iota> 3))
           (vec_nth x (\<iota> 4)) (vec_nth x (\<iota> 5)) (vec_nth x (\<iota> 6))"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence sub: "B \<subseteq> {x. ttprod \<iota> x = 0}"
    using ttprod_nz_iff by blast
  obtain xw where xw: "triples_transverse
           (vec_nth xw (\<iota> 1)) (vec_nth xw (\<iota> 2)) (vec_nth xw (\<iota> 3))
           (vec_nth xw (\<iota> 4)) (vec_nth xw (\<iota> 5)) (vec_nth xw (\<iota> 6))"
    using triples_transverse_witness[OF inji] by blast
  have exw: "\<exists>x\<in>UNIV. ttprod \<iota> x \<noteq> 0"
    using xw ttprod_nz_iff by blast
  have "interior (closure {x \<in> UNIV. ttprod \<iota> x = 0}) = {}"
    by (rule real_analytic_nowhere_dense_zeros[OF real_analytic_on_ttprod
          connected_UNIV exw])
  moreover have "B \<subseteq> interior (closure {x \<in> UNIV. ttprod \<iota> x = 0})"
  proof (rule interior_maximal[OF _ Bo])
    show "B \<subseteq> closure {x \<in> UNIV. ttprod \<iota> x = 0}"
      using sub closure_subset by fastforce
  qed
  ultimately show False using Bne by blast
qed

subsection \<open>The reduction: \<open>wit\<close> from the branch core\<close>

text \<open>\<^bold>\<open>The final 4b reduction.\<close>  The hypothesis \<open>wit_core\<close> below is the exact shape
  the Case-B branch corollaries establish: on a connected analytic critical chart
  along which the steered wavevector is nonzero AND a FIXED triple of elements stays
  good, the moment determinant is not identically zero.  Everything else --- finding
  a transverse point on the chart (the product certificate), selecting the good
  triple for the local wavevector (@{thm two_triple_cover_pointwise}), and making
  goodness persist (@{thm triple_good_chart_persist}) --- is discharged here.  Note
  the reduction needs \<open>6 \<le> CARD('n)\<close> only to pick the six indices.\<close>

theorem dip_wit_reduction:
  fixes B :: "((real^2)^'n::finite) set" and g :: "(real^2)^'n \<Rightarrow> real^2"
    and x0 :: "(real^2)^'n" and \<omega>b \<omega>0 \<omega>s :: "real^2"
  assumes n6: "6 \<le> CARD('n)"
    and wit_core: "\<And>(B'::((real^2)^'n) set) g' (i::'n) j k.
          open B' \<Longrightarrow> connected B' \<Longrightarrow> B' \<noteq> {} \<Longrightarrow>
          real_analytic_on g' B' \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x) = 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g' x) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g' x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)) \<Longrightarrow>
          \<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g' x)) x \<noteq> 0"
    and Bo: "open B" and Bc: "connected B" and xB: "x0 \<in> B"
    and gana: "real_analytic_on g B" and gx0: "g x0 = \<omega>b"
    and grad0: "\<And>x. x \<in> B \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
    and cnz: "\<And>x. x \<in> B \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0"
    and dnz: "\<And>x. x \<in> B \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0"
  shows "\<exists>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
proof -
  \<comment> \<open>six distinct indices\<close>
  have c6: "CARD(6) \<le> CARD('n)" using n6 by simp
  obtain \<iota> :: "6 \<Rightarrow> 'n" where inji: "inj \<iota>"
    using card_le_inj[OF finite_class.finite_UNIV finite_class.finite_UNIV c6]
    by (auto simp: inj_def)
  \<comment> \<open>a transverse point on the chart\<close>
  have Bne: "B \<noteq> {}" using xB by blast
  obtain x1 where x1B: "x1 \<in> B" and tt: "triples_transverse
           (vec_nth x1 (\<iota> 1)) (vec_nth x1 (\<iota> 2)) (vec_nth x1 (\<iota> 3))
           (vec_nth x1 (\<iota> 4)) (vec_nth x1 (\<iota> 5)) (vec_nth x1 (\<iota> 6))"
    using transverse_point_in_open[OF inji Bo Bne] by blast
  \<comment> \<open>the local wavevector is good for one of the two triples\<close>
  have c1: "cvec_dip \<omega>0 \<omega>s (g x1) \<noteq> 0" by (rule cnz[OF x1B])
  from two_triple_cover_pointwise[OF tt c1]
  have "triple_good (cvec_dip \<omega>0 \<omega>s (g x1))
          (vec_nth x1 (\<iota> 1)) (vec_nth x1 (\<iota> 2)) (vec_nth x1 (\<iota> 3))
      \<or> triple_good (cvec_dip \<omega>0 \<omega>s (g x1))
          (vec_nth x1 (\<iota> 4)) (vec_nth x1 (\<iota> 5)) (vec_nth x1 (\<iota> 6))" .
  then obtain i j k where good1: "triple_good (cvec_dip \<omega>0 \<omega>s (g x1))
          (vec_nth x1 i) (vec_nth x1 j) (vec_nth x1 k)"
    by blast
  \<comment> \<open>persist goodness on a sub-chart around the transverse point\<close>
  show ?thesis
  proof (rule triple_good_chart_persist[OF Bo x1B gana good1])
    fix B' assume B'o: "open B'" and B'c: "connected B'" and x1B': "x1 \<in> B'"
      and B'sub: "B' \<subseteq> B"
      and goodB': "\<And>x. x \<in> B' \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g x))
             (vec_nth x i) (vec_nth x j) (vec_nth x k)"
    have B'ne: "B' \<noteq> {}" using x1B' by blast
    have ganaB': "real_analytic_on g B'"
      by (rule real_analytic_on_open_subset[OF gana B'o B'sub])
    have Wgrad: "\<And>x. x \<in> B' \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
      using grad0 B'sub by blast
    have Wcnz: "\<And>x. x \<in> B' \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0"
      using cnz B'sub by blast
    have Wdnz: "\<And>x. x \<in> B' \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0"
      using dnz B'sub by blast
    have "\<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
      by (rule wit_core[of B' g i j k, OF B'o B'c B'ne ganaB' Wgrad Wcnz Wdnz goodB'])
    thus ?thesis using B'sub by blast
  qed
qed

end
