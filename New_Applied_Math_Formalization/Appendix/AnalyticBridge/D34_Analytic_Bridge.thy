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
  in the two Robust3 proof holes.\<close>

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


section \<open>Layer 4b: the branch case scaffold for \<open>wit_core\<close>\<close>

text \<open>\<open>det H \<noteq> 0\<close> makes the first Hessian row nonzero, so at any point of a
  \<open>wit_core\<close> chart either \<open>H\<^sub>1\<^sub>1 \<noteq> 0\<close> or \<open>H\<^sub>1\<^sub>2 \<noteq> 0\<close>; if \<open>H\<^sub>1\<^sub>1 = 0\<close> but \<open>H\<^sub>2\<^sub>2 \<noteq> 0\<close> we
  route through the \<open>H\<^sub>2\<^sub>2\<close> branch instead (matching the paper's branch families).
  Each nonvanishing persists on a shrunk sub-chart by the standard continuity
  shrink on the (analytic) entry field.  Hence \<open>wit_core\<close>'s conclusion follows
  from THREE branch hypotheses, each with the full chart package plus one Hessian
  entry nonvanishing ALONG the chart: the exact standing hypotheses of the paper's
  \<open>H\<^sub>1\<^sub>1\<close>-branch (\<open>cor:H11-closed\<close>), \<open>H\<^sub>2\<^sub>2\<close>-branches (\<open>cor:vpair22-full\<close> /
  \<open>cor:Lambda-closed\<close> / \<open>cor:uphi-exhausted\<close>), and the diagonal-degenerate
  \<open>H\<^sub>1\<^sub>2\<close>-residual.\<close>

lemma real_analytic_on_HessU_entry_chart:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2" and k l :: 2
  assumes Bo: "open B" and gana: "real_analytic_on g B"
  shows "real_analytic_on (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l) B"
proof -
  have idB: "real_analytic_on (\<lambda>x::(real^2)^'n. x) B"
    by (rule real_analytic_on_bounded_linear[OF Bo bounded_linear_ident])
  have pairB: "real_analytic_on (\<lambda>x::(real^2)^'n. (x, g x)) B"
    by (rule real_analytic_on_Pair[OF idB gana])
  have "real_analytic_on (\<lambda>x::(real^2)^'n.
          (\<lambda>q::((real^2)^'n) \<times> (real^2).
             vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip (fst q) (snd q)) k) l)
            (x, g x)) B"
    by (rule real_analytic_on_compose[OF pairB real_analytic_on_HessU_dip_entry subset_UNIV])
  thus ?thesis by simp
qed

text \<open>The generic sub-chart shrink on a nonvanishing Hessian entry.\<close>

lemma HessU_entry_chart_shrink:
  fixes g :: "(real^2)^'n::finite \<Rightarrow> real^2" and x1 :: "(real^2)^'n" and k l :: 2
  assumes Bo: "open B" and x1B: "x1 \<in> B" and gana: "real_analytic_on g B"
    and e1: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) k) l \<noteq> 0"
  obtains B' where
    "open B'" and "connected B'" and "x1 \<in> B'" and "B' \<subseteq> B"
    and "\<And>x. x \<in> B' \<Longrightarrow>
           vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l \<noteq> 0"
proof -
  have hana: "real_analytic_on (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l) B"
    by (rule real_analytic_on_HessU_entry_chart[OF Bo gana])
  have hisC: "isCont (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l) x"
    if "x \<in> B" for x
    by (rule has_derivative_continuous[OF
          real_analytic_on_has_derivative_Dblinfun[OF hana that]])
  have hcont: "continuous_on B (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l)"
    using hisC continuous_at_imp_continuous_on by blast
  have Sopen: "open (B \<inter> (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l) -` (- {0}))"
    by (rule continuous_open_preimage[OF hcont Bo])
       (rule open_Compl[OF closed_singleton])
  have x1S: "x1 \<in> B \<inter> (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l) -` (- {0})"
    using x1B e1 by simp
  obtain \<epsilon> where e0: "0 < \<epsilon>" and esub: "ball x1 \<epsilon> \<subseteq> B \<inter> (\<lambda>x.
      vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l) -` (- {0})"
    using openE[OF Sopen x1S] by blast
  show ?thesis
  proof (rule that[of "ball x1 \<epsilon>"])
    show "open (ball x1 \<epsilon>)" by simp
    show "connected (ball x1 \<epsilon>)" by simp
    show "x1 \<in> ball x1 \<epsilon>" by (simp add: centre_in_ball e0)
    show "ball x1 \<epsilon> \<subseteq> B" using esub by auto
    show "\<And>x. x \<in> ball x1 \<epsilon> \<Longrightarrow>
        vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) k) l \<noteq> 0"
      using esub by auto
  qed
qed

text \<open>\<^bold>\<open>The scaffold.\<close>  \<open>wit_core\<close>'s conclusion from the three branch hypotheses.\<close>

theorem dip_wit_core_scaffold:
  fixes B :: "((real^2)^'n::finite) set" and g :: "(real^2)^'n \<Rightarrow> real^2"
    and i j k :: 'n and \<omega>0 \<omega>s :: "real^2"
  assumes Bo: "open B" and Bc: "connected B" and Bne: "B \<noteq> {}"
    and gana: "real_analytic_on g B"
    and grad0: "\<And>x. x \<in> B \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0"
    and cnz: "\<And>x. x \<in> B \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0"
    and dnz: "\<And>x. x \<in> B \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0"
    and good: "\<And>x. x \<in> B \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)"
    and brH11: "\<And>(B'::((real^2)^'n) set) g'. open B' \<Longrightarrow> connected B' \<Longrightarrow> B' \<noteq> {} \<Longrightarrow>
          real_analytic_on g' B' \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x) = 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g' x) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g' x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow>
             vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) 1) 1 \<noteq> 0) \<Longrightarrow>
          \<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g' x)) x \<noteq> 0"
    and brH22: "\<And>(B'::((real^2)^'n) set) g'. open B' \<Longrightarrow> connected B' \<Longrightarrow> B' \<noteq> {} \<Longrightarrow>
          real_analytic_on g' B' \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x) = 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g' x) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g' x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow>
             vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) 2) 2 \<noteq> 0) \<Longrightarrow>
          \<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g' x)) x \<noteq> 0"
    and brH12: "\<And>(B'::((real^2)^'n) set) g'. open B' \<Longrightarrow> connected B' \<Longrightarrow> B' \<noteq> {} \<Longrightarrow>
          real_analytic_on g' B' \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x) = 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g' x) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g' x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow>
             vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g' x)) 1) 2 \<noteq> 0) \<Longrightarrow>
          \<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g' x)) x \<noteq> 0"
  shows "\<exists>x\<in>B. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
proof -
  obtain x1 where x1B: "x1 \<in> B" using Bne by blast
  \<comment> \<open>the pointwise entry dichotomy from \<open>det H \<noteq> 0\<close>\<close>
  have entry_cases: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 1) 1 \<noteq> 0
      \<or> vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 2) 2 \<noteq> 0
      \<or> vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 1) 2 \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence z: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 1) 1 = 0"
      "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 2) 2 = 0"
      "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 1) 2 = 0"
      by auto
    have "det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) = 0"
      by (simp add: det_2 z)
    with dnz[OF x1B] show False by simp
  qed
  \<comment> \<open>route each case through the matching branch on a shrunk sub-chart\<close>
  have package: "\<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
    if B'o: "open B'" and B'c: "connected B'" and x1B': "x1 \<in> B'" and B'sub: "B' \<subseteq> B"
    and br: "open B' \<Longrightarrow> connected B' \<Longrightarrow> B' \<noteq> {} \<Longrightarrow>
          real_analytic_on g B' \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x) = 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> cvec_dip \<omega>0 \<omega>s (g x) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> det (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) \<noteq> 0) \<Longrightarrow>
          (\<And>x. x \<in> B' \<Longrightarrow> triple_good (cvec_dip \<omega>0 \<omega>s (g x))
                 (vec_nth x i) (vec_nth x j) (vec_nth x k)) \<Longrightarrow>
          \<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
    for B'
  proof -
    have B'ne: "B' \<noteq> {}" using x1B' by blast
    have ganaB': "real_analytic_on g B'"
      by (rule real_analytic_on_open_subset[OF gana B'o B'sub])
    show ?thesis
      by (rule br[OF B'o B'c B'ne ganaB'])
         (use grad0 cnz dnz good B'sub in blast)+
  qed
  from entry_cases show ?thesis
  proof (elim disjE)
    assume e1: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 1) 1 \<noteq> 0"
    show ?thesis
    proof (rule HessU_entry_chart_shrink[OF Bo x1B gana e1])
      fix B' assume B'o: "open B'" and B'c: "connected B'" and x1B': "x1 \<in> B'"
        and B'sub: "B' \<subseteq> B"
        and eB': "\<And>x. x \<in> B' \<Longrightarrow>
            vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) 1) 1 \<noteq> 0"
      have "\<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
        by (rule package[OF B'o B'c x1B' B'sub])
           (rule brH11[of B' g], assumption+, rule eB', assumption)
      thus ?thesis using B'sub by blast
    qed
  next
    assume e2: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 2) 2 \<noteq> 0"
    show ?thesis
    proof (rule HessU_entry_chart_shrink[OF Bo x1B gana e2])
      fix B' assume B'o: "open B'" and B'c: "connected B'" and x1B': "x1 \<in> B'"
        and B'sub: "B' \<subseteq> B"
        and eB': "\<And>x. x \<in> B' \<Longrightarrow>
            vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) 2) 2 \<noteq> 0"
      have "\<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
        by (rule package[OF B'o B'c x1B' B'sub])
           (rule brH22[of B' g], assumption+, rule eB', assumption)
      thus ?thesis using B'sub by blast
    qed
  next
    assume e3: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x1 (g x1)) 1) 2 \<noteq> 0"
    show ?thesis
    proof (rule HessU_entry_chart_shrink[OF Bo x1B gana e3])
      fix B' assume B'o: "open B'" and B'c: "connected B'" and x1B': "x1 \<in> B'"
        and B'sub: "B' \<subseteq> B"
        and eB': "\<And>x. x \<in> B' \<Longrightarrow>
            vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x (g x)) 1) 2 \<noteq> 0"
      have "\<exists>x\<in>B'. mstarg (cvec_dip \<omega>0 \<omega>s (g x)) x \<noteq> 0"
        by (rule package[OF B'o B'c x1B' B'sub])
           (rule brH12[of B' g], assumption+, rule eB', assumption)
      thus ?thesis using B'sub by blast
    qed
  qed
qed


section \<open>Layer 4b, H11 certificate ground layer: single-slot moment derivative laws\<close>

text \<open>The branch certificates differentiate the gauge-fixed \<open>\<Phi>\<close>/\<open>H\<close> formulas in the
  \<open>u\<close>/\<open>v\<close>-slice directions of the good triple: configuration variations supported at
  ONE element, parallel or perpendicular to \<open>c\<close>.  This theory provides the complete
  single-slot calculus for the six moment \<open>x\<close>-derivatives:
  \<^enum> \<open>slot j v\<close> (the variation moving only element \<open>j\<close> by \<open>v\<close>) and \<open>perp2 c\<close>
    (the \<open>\<kappa>\<close>-scaled \<open>v\<close>-direction);
  \<^enum> the master phase law \<open>d_phase_slot\<close> and the six collapsed moment laws
    (\<open>d_A_moment_x_slot\<close>, \<dots>) --- each derivative is a SINGLE surviving term;
  \<^enum> the perpendicular corollaries (\<open>c \<bullet> v = 0\<close>): the phase derivative dies and only
    the weight term survives --- the source of \<open>\<partial>\<^sub>v\<^sub>j \<Phi>\<^sub>2 = -2ag s\<^sub>j\<close>,
    \<open>\<partial>\<^sub>v\<^sub>j H\<^sub>1\<^sub>2 = 2gc\<^sub>j(a\<^sub>1 - au\<^sub>j)\<close>, \<open>\<partial>\<^sub>v\<^sub>j H\<^sub>2\<^sub>2 = 4gc\<^sub>j(a\<^sub>2 - av\<^sub>j)\<close> and
    \<open>H\<^sub>1\<^sub>1\<close>/\<open>\<Phi>\<^sub>1\<close> \<open>v\<close>-independence in \<open>prop:vpair11\<close>;
  \<^enum> the glue \<open>D*_paper_x = d_*_moment_x\<close> identifying the two derivative-entry
    families in scope.\<close>

subsection \<open>The slot direction and the perpendicular vector\<close>

definition slot :: "'n::finite \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n" where
  "slot j v = (\<chi> m. if m = j then v else 0)"

lemma slot_nth: "vec_nth (slot j v) n = (if n = j then v else 0)"
  by (simp add: slot_def)

definition perp2 :: "real^2 \<Rightarrow> real^2" where
  "perp2 c = vector [- vec_nth c 2, vec_nth c 1]"

lemma perp2_orth: "c \<bullet> perp2 c = 0"
  by (simp add: perp2_def inner_vec_def sum_2)

lemma perp2_nz:
  assumes "c \<noteq> (0::real^2)"
  shows "perp2 c \<noteq> 0"
proof
  assume z: "perp2 c = 0"
  have "vec_nth (perp2 c) 1 = - vec_nth c 2" and "vec_nth (perp2 c) 2 = vec_nth c 1"
    by (simp_all add: perp2_def)
  with z have "vec_nth c 1 = 0" "vec_nth c 2 = 0" by auto
  hence "vec_nth c m = 0" for m using exhaust_2[of m] by auto
  hence "c = 0" by (simp add: Finite_Cartesian_Product.vec_eq_iff)
  with assms show False by simp
qed

subsection \<open>The master phase law and the six slot laws\<close>

lemma d_phase_slot:
  "d_phase c x (slot j v) n
     = (if n = j then -(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))) else 0)"
  by (simp add: d_phase_def slot_nth)

lemma d_A_moment_x_slot:
  "d_A_moment_x x c (slot j v) = -(c \<bullet> v) *\<^sub>R (\<i> * phase c x j)"
proof -
  have "d_A_moment_x x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j then -(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))) else 0)"
    unfolding d_A_moment_x_def by (rule sum.cong[OF refl]) (simp add: d_phase_slot)
  also have "\<dots> = -(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j)))"
    by (simp add: sum.delta')
  finally show ?thesis by (simp add: phase_def)
qed

lemma d_M1_moment_x_slot:
  "d_M1_moment_x x c (slot j v)
     = of_real (vec_nth v 1) * phase c x j
       + of_real (vec_nth (vec_nth x j) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have "d_M1_moment_x x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (vec_nth v 1) * phase c x n
             + of_real (vec_nth (vec_nth x n) 1)
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding d_M1_moment_x_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth)
  also have "\<dots> = of_real (vec_nth v 1) * phase c x j
       + of_real (vec_nth (vec_nth x j) 1) * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis by (simp add: phase_def)
qed

lemma d_M2_moment_x_slot:
  "d_M2_moment_x x c (slot j v)
     = of_real (vec_nth v 2) * phase c x j
       + of_real (vec_nth (vec_nth x j) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have "d_M2_moment_x x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (vec_nth v 2) * phase c x n
             + of_real (vec_nth (vec_nth x n) 2)
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding d_M2_moment_x_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth)
  also have "\<dots> = of_real (vec_nth v 2) * phase c x j
       + of_real (vec_nth (vec_nth x j) 2) * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis by (simp add: phase_def)
qed

lemma d_M11_moment_x_slot:
  "d_M11_moment_x x c (slot j v)
     = of_real (2 * vec_nth (vec_nth x j) 1 * vec_nth v 1) * phase c x j
       + of_real ((vec_nth (vec_nth x j) 1)\<^sup>2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have "d_M11_moment_x x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (2 * vec_nth (vec_nth x n) 1 * vec_nth v 1) * phase c x n
             + of_real ((vec_nth (vec_nth x n) 1)\<^sup>2)
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding d_M11_moment_x_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth)
  also have "\<dots> = of_real (2 * vec_nth (vec_nth x j) 1 * vec_nth v 1) * phase c x j
       + of_real ((vec_nth (vec_nth x j) 1)\<^sup>2)
           * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis by (simp add: phase_def)
qed

lemma d_M12_moment_x_slot:
  "d_M12_moment_x x c (slot j v)
     = of_real (dw_M12 (vec_nth x j) v) * phase c x j
       + of_real (w_M12 (vec_nth x j)) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have dwz: "dw_M12 p 0 = 0" for p :: "real^2"
    by (simp add: dw_M12_def)
  have "d_M12_moment_x x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (dw_M12 (vec_nth x n) v) * phase c x n
             + of_real (w_M12 (vec_nth x n))
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding d_M12_moment_x_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth dwz)
  also have "\<dots> = of_real (dw_M12 (vec_nth x j) v) * phase c x j
       + of_real (w_M12 (vec_nth x j))
           * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis by (simp add: phase_def)
qed

lemma d_M22_moment_x_slot:
  "d_M22_moment_x x c (slot j v)
     = of_real (2 * vec_nth (vec_nth x j) 2 * vec_nth v 2) * phase c x j
       + of_real ((vec_nth (vec_nth x j) 2)\<^sup>2) * (-(c \<bullet> v) *\<^sub>R (\<i> * phase c x j))"
proof -
  have "d_M22_moment_x x c (slot j v)
      = (\<Sum>n\<in>UNIV. if n = j
          then of_real (2 * vec_nth (vec_nth x n) 2 * vec_nth v 2) * phase c x n
             + of_real ((vec_nth (vec_nth x n) 2)\<^sup>2)
                 * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x n))))
          else 0)"
    unfolding d_M22_moment_x_def
    by (rule sum.cong[OF refl]) (simp add: d_phase_slot slot_nth)
  also have "\<dots> = of_real (2 * vec_nth (vec_nth x j) 2 * vec_nth v 2) * phase c x j
       + of_real ((vec_nth (vec_nth x j) 2)\<^sup>2)
           * (-(c \<bullet> v) *\<^sub>R (\<i> * cis (-(c \<bullet> vec_nth x j))))"
    by (simp add: sum.delta')
  finally show ?thesis by (simp add: phase_def)
qed

subsection \<open>Perpendicular slots: the phase derivative dies\<close>

lemma d_A_moment_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "d_A_moment_x x c (slot j v) = 0"
  by (simp add: d_A_moment_x_slot assms)

lemma d_M1_moment_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "d_M1_moment_x x c (slot j v) = of_real (vec_nth v 1) * phase c x j"
  by (simp add: d_M1_moment_x_slot assms)

lemma d_M2_moment_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "d_M2_moment_x x c (slot j v) = of_real (vec_nth v 2) * phase c x j"
  by (simp add: d_M2_moment_x_slot assms)

lemma d_M11_moment_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "d_M11_moment_x x c (slot j v)
       = of_real (2 * vec_nth (vec_nth x j) 1 * vec_nth v 1) * phase c x j"
  by (simp add: d_M11_moment_x_slot assms)

lemma d_M12_moment_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "d_M12_moment_x x c (slot j v)
       = of_real (dw_M12 (vec_nth x j) v) * phase c x j"
  by (simp add: d_M12_moment_x_slot assms)

lemma d_M22_moment_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "d_M22_moment_x x c (slot j v)
       = of_real (2 * vec_nth (vec_nth x j) 2 * vec_nth v 2) * phase c x j"
  by (simp add: d_M22_moment_x_slot assms)

subsection \<open>Glue: the two derivative-entry families coincide\<close>

lemma DA_paper_eq_d_moment: "DA_paper_x x c h = d_A_moment_x x c h"
  by (simp add: DA_paper_x_def d_A_moment_x_def)

lemma DM1_paper_eq_d_moment: "DM1_paper_x x c h = d_M1_moment_x x c h"
  by (simp add: DM1_paper_x_def d_M1_moment_x_def)

lemma DM2_paper_eq_d_moment: "DM2_paper_x x c h = d_M2_moment_x x c h"
  by (simp add: DM2_paper_x_def d_M2_moment_x_def)

lemma DM11_paper_eq_d_moment: "DM11_paper_x x c h = d_M11_moment_x x c h"
  by (simp add: DM11_paper_x_def d_M11_moment_x_def)

lemma DM12_paper_eq_d_moment: "DM12_paper_x x c h = d_M12_moment_x x c h"
  by (simp add: DM12_paper_x_def d_M12_moment_x_def)

lemma DM22_paper_eq_d_moment: "DM22_paper_x x c h = d_M22_moment_x x c h"
  by (simp add: DM22_paper_x_def d_M22_moment_x_def)


section \<open>Layer 4b (corrected Case-B side): perp-slot derivatives of the gradient field\<close>

text \<open>ARCHITECTURE NOTE (2026-07-07).  The true D34 target
  (\<open>m5_D34_residual\<close>, Robust3) RETAINS \<open>det HessU = 0\<close> and \<open>A_cart \<noteq> 0\<close>; the two proof holes
  were stated for the ENLARGED residual (\<open>m5_D34_subset_mstarg_residual\<close> is a
  pure \<open>blast\<close> weakening).  The needed bad set is thus EXACTLY the paper's Case-B set,
  where the branch certificates (built on \<open>\<Phi>\<^sub>3 = det H = 0\<close>) apply --- at FIXED \<open>\<omega>\<close>,
  with rank-3 \<open>x\<close>-charts, no \<open>\<omega>\<close>-graph needed.  This theory delivers the first
  corrected-path derivative brick: the \<open>x\<close>-derivative of the gradient field
  \<open>y \<mapsto> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>\<close> in a PERPENDICULAR slot direction,
  in invariant form
    \<open>\<partial>\<^bsub>slot m v\<^esub> \<Phi>\<^sub>j = 2 g (\<gamma>\<^sub>j \<bullet> v) Im(cnj A \<cdot> \<phi>\<^sub>m)\<close>,
  \<open>\<gamma>\<^sub>j = Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)\<close> --- the paper's \<open>\<partial>\<^sub>v\<^sub>j \<Phi>\<^sub>2 = -2ag s\<^sub>j\<close> after the
  \<open>b = 0, a > 0\<close> gauge and \<open>c\<close>-frame specialisation.\<close>

subsection \<open>\<open>dEjm\<close> on a tangent with vanishing first slot\<close>

lemma dEjm_zero1:
  fixes M0 \<delta> :: "complex^6"
  assumes z1: "vec_nth \<delta> 1 = 0"
  shows "dEjm p g c1 c2 M0 \<delta>
       = 2 * g * Im (cnj (vec_nth M0 1)
           * (complex_of_real c1 * vec_nth \<delta> 2 + complex_of_real c2 * vec_nth \<delta> 3))"
proof -
  have key: "Re (cnj (vec_nth M0 1) * ((- \<i>) * complex_of_real c1 * vec_nth \<delta> 2
                 + (- \<i>) * complex_of_real c2 * vec_nth \<delta> 3))
           = Im (cnj (vec_nth M0 1) * (complex_of_real c1 * vec_nth \<delta> 2
                 + complex_of_real c2 * vec_nth \<delta> 3))"
  proof -
    have "cnj (vec_nth M0 1) * ((- \<i>) * complex_of_real c1 * vec_nth \<delta> 2
             + (- \<i>) * complex_of_real c2 * vec_nth \<delta> 3)
        = (- \<i>) * (cnj (vec_nth M0 1) * (complex_of_real c1 * vec_nth \<delta> 2
             + complex_of_real c2 * vec_nth \<delta> 3))"
      by (simp add: algebra_simps)
    thus ?thesis by simp
  qed
  show ?thesis
    unfolding dEjm_def by (simp add: z1 key algebra_simps)
qed

subsection \<open>The moment tangent of a perpendicular slot\<close>

lemma DM_paper_x_perp_slot_1:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "vec_nth (DM_paper_x x c (slot m v)) 1 = 0"
proof -
  have "vec_nth (DM_paper_x x c (slot m v)) 1 = DA_paper_x x c (slot m v)"
    by (simp add: DM_paper_x_def)
  also have "\<dots> = d_A_moment_x x c (slot m v)"
    by (rule DA_paper_eq_d_moment)
  also have "\<dots> = 0"
    by (rule d_A_moment_x_perp[OF perp])
  finally show ?thesis .
qed

lemma DM_paper_x_perp_slot_2:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "vec_nth (DM_paper_x x c (slot m v)) 2 = of_real (vec_nth v 1) * phase c x m"
proof -
  have "vec_nth (DM_paper_x x c (slot m v)) 2 = DM1_paper_x x c (slot m v)"
    by (simp add: DM_paper_x_def)
  also have "\<dots> = d_M1_moment_x x c (slot m v)"
    by (rule DM1_paper_eq_d_moment)
  also have "\<dots> = of_real (vec_nth v 1) * phase c x m"
    by (rule d_M1_moment_x_perp[OF perp])
  finally show ?thesis .
qed

lemma DM_paper_x_perp_slot_3:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "vec_nth (DM_paper_x x c (slot m v)) 3 = of_real (vec_nth v 2) * phase c x m"
proof -
  have "vec_nth (DM_paper_x x c (slot m v)) 3 = DM2_paper_x x c (slot m v)"
    by (simp add: DM_paper_x_def)
  also have "\<dots> = d_M2_moment_x x c (slot m v)"
    by (rule DM2_paper_eq_d_moment)
  also have "\<dots> = of_real (vec_nth v 2) * phase c x m"
    by (rule d_M2_moment_x_perp[OF perp])
  finally show ?thesis .
qed

subsection \<open>The invariant perp-slot derivative of the gradient field\<close>

lemma dEjm_perp_slot_value:
  fixes c v :: "real^2" and \<gamma> :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "dEjm p g (vec_nth \<gamma> 1) (vec_nth \<gamma> 2) (M_paper x c) (DM_paper_x x c (slot m v))
       = 2 * g * (\<gamma> \<bullet> v) * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m)"
proof -
  have "dEjm p g (vec_nth \<gamma> 1) (vec_nth \<gamma> 2) (M_paper x c) (DM_paper_x x c (slot m v))
      = 2 * g * Im (cnj (vec_nth (M_paper x c) 1)
          * (complex_of_real (vec_nth \<gamma> 1) * (of_real (vec_nth v 1) * phase c x m)
           + complex_of_real (vec_nth \<gamma> 2) * (of_real (vec_nth v 2) * phase c x m)))"
    by (simp add: dEjm_zero1[OF DM_paper_x_perp_slot_1[OF perp]]
        DM_paper_x_perp_slot_2[OF perp] DM_paper_x_perp_slot_3[OF perp])
  also have "complex_of_real (vec_nth \<gamma> 1) * (of_real (vec_nth v 1) * phase c x m)
           + complex_of_real (vec_nth \<gamma> 2) * (of_real (vec_nth v 2) * phase c x m)
      = of_real (\<gamma> \<bullet> v) * phase c x m"
    by (simp add: inner_vec_def sum_2 of_real_add of_real_mult algebra_simps)
  also have "2 * g * Im (cnj (vec_nth (M_paper x c) 1) * (of_real (\<gamma> \<bullet> v) * phase c x m))
      = 2 * g * (\<gamma> \<bullet> v) * Im (cnj (vec_nth (M_paper x c) 1) * phase c x m)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

theorem gradU_dip_xderiv_perp_slot:
  fixes x :: "(real^2)^'n::finite" and v :: "real^2" and m :: 'n and \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "(\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v)))
       = (\<chi> j. 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
             * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                   * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))"
proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 2
  show "vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>))
                (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) j
       = vec_nth (\<chi> j. 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1) \<bullet> v)
             * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1)
                   * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)) j"
    by (simp add: dEjm_perp_slot_value[OF perp])
qed


section \<open>Layer 4b (Case-B path): perp-slot \<open>x\<close>-derivatives of the Hessian blocks\<close>

text \<open>The branch certificates differentiate \<open>H\<^sub>1\<^sub>2\<close>, \<open>H\<^sub>2\<^sub>2\<close> (and \<open>\<Phi>\<^sub>3 = det H\<close>) in
  \<open>v\<close>-slot directions.  Through @{thm HessU_dip_entry_moments} every \<open>x\<close>-dependence of
  a Hessian entry routes through THREE blocks at fixed \<open>c\<close>: the pattern value
  \<open>V = |A|\<^sup>2\<close>, the \<open>c\<close>-gradient components \<open>(\<nabla>\<^sub>cV)\<^sub>i\<close>, and the \<open>Hcmat\<close> entries.  This
  theory delivers their explicit \<open>x\<close>-derivatives (at fixed \<open>c\<close>) and the perp-slot
  values, in invariant form:
  \<^enum> \<open>\<partial>\<^bsub>slot m v\<^esub> V = 0\<close>;
  \<^enum> \<open>\<partial>\<^bsub>slot m v\<^esub> (\<nabla>\<^sub>cV)\<^sub>i = 2 v\<^sub>i Im(cnj A \<cdot> \<phi>\<^sub>m)\<close>;
  \<^enum> \<open>\<partial>\<^bsub>slot m v\<^esub> Hcmat\<^sub>k\<^sub>l = 2[v\<^sub>l Re(cnj \<phi>\<^sub>m M\<^sub>k) + v\<^sub>k Re(cnj M\<^sub>l \<phi>\<^sub>m)
        - (v\<^sub>k x\<^sub>l + x\<^sub>k v\<^sub>l) Re(cnj A \<phi>\<^sub>m)]\<close>
  --- the gauge/frame-free generators of the paper's \<open>\<partial>\<^sub>v\<^sub>j H\<^sub>1\<^sub>2 = 2gc\<^sub>j(a\<^sub>1-au\<^sub>j)\<close>,
  \<open>\<partial>\<^sub>v\<^sub>j H\<^sub>2\<^sub>2 = 4gc\<^sub>j(a\<^sub>2-av\<^sub>j)\<close> and the \<open>H\<^sub>1\<^sub>1\<close> \<open>v\<close>-behaviour in \<open>prop:vpair11\<close> /
  \<open>prop:vblock\<close>.\<close>

subsection \<open>Glue: the \<open>c\<close>-pattern moment functions are the paper moments\<close>

lemma Mcfun_eq_M1_moment: "Mcfun x c 1 = M1_moment x c"
  by (simp add: Mcfun_def M1_moment_def phase_def)

lemma Mcfun_eq_M2_moment: "Mcfun x c 2 = M2_moment x c"
  by (simp add: Mcfun_def M2_moment_def phase_def)

lemma M2cfun_eq_M11_moment: "M2cfun x c 1 1 = M11_moment x c"
  unfolding M2cfun_def M11_moment_def phase_def
  by (rule sum.cong[OF refl]) (simp add: power2_eq_square)

lemma M2cfun_eq_M12_moment: "M2cfun x c 1 2 = M12_moment x c"
  unfolding M2cfun_def M12_moment_def phase_def w_M12_def
  by (rule sum.cong[OF refl]) simp

lemma M2cfun_eq_M12_moment': "M2cfun x c 2 1 = M12_moment x c"
  unfolding M2cfun_def M12_moment_def phase_def w_M12_def
  by (rule sum.cong[OF refl]) (simp add: ac_simps)

lemma M2cfun_eq_M22_moment: "M2cfun x c 2 2 = M22_moment x c"
  unfolding M2cfun_def M22_moment_def phase_def
  by (rule sum.cong[OF refl]) (simp add: power2_eq_square)

subsection \<open>Uniform derivative entries for the \<open>c\<close>-pattern moments\<close>

definition dMcfun_x :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> (real^2)^'n \<Rightarrow> complex" where
  "dMcfun_x x c k = (if k = 1 then d_M1_moment_x x c else d_M2_moment_x x c)"

definition dM2cfun_x :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> (real^2)^'n \<Rightarrow> complex" where
  "dM2cfun_x x c k l =
     (if k = 1 then (if l = 1 then d_M11_moment_x x c else d_M12_moment_x x c)
      else (if l = 1 then d_M12_moment_x x c else d_M22_moment_x x c))"

lemma has_derivative_Afun_x:
  "((\<lambda>y. Afun y c) has_derivative (\<lambda>h. d_A_moment_x x c h)) (at x)"
proof -
  have F: "((\<lambda>y. A_moment y c) has_derivative (\<lambda>h. d_A_moment_x x c h)) (at x)"
    by (rule has_derivative_A_moment_x)
  have eqn: "(\<lambda>y. Afun y c) = (\<lambda>y. A_moment y c)"
    by (rule ext) (simp add: Afun_eq_A_moment)
  show ?thesis unfolding eqn by (rule F)
qed

lemma has_derivative_Mcfun_x:
  "((\<lambda>y. Mcfun y c k) has_derivative dMcfun_x x c k) (at x)"
proof -
  consider "k = (1::2)" | "k = 2" using exhaust_2 by blast
  thus ?thesis
  proof cases
    case 1
    have F: "((\<lambda>y. M1_moment y c) has_derivative (\<lambda>h. d_M1_moment_x x c h)) (at x)"
      by (rule has_derivative_M1_moment_x)
    have eqn: "(\<lambda>y. Mcfun y c k) = (\<lambda>y. M1_moment y c)"
      using 1 by (simp add: fun_eq_iff Mcfun_eq_M1_moment)
    have dEq: "dMcfun_x x c k = (\<lambda>h. d_M1_moment_x x c h)"
      using 1 by (simp add: dMcfun_x_def)
    show ?thesis unfolding eqn dEq by (rule F)
  next
    case 2
    have F: "((\<lambda>y. M2_moment y c) has_derivative (\<lambda>h. d_M2_moment_x x c h)) (at x)"
      by (rule has_derivative_M2_moment_x)
    have eqn: "(\<lambda>y. Mcfun y c k) = (\<lambda>y. M2_moment y c)"
      using 2 by (simp add: fun_eq_iff Mcfun_eq_M2_moment)
    have dEq: "dMcfun_x x c k = (\<lambda>h. d_M2_moment_x x c h)"
      using 2 by (simp add: dMcfun_x_def)
    show ?thesis unfolding eqn dEq by (rule F)
  qed
qed

lemma has_derivative_M2cfun_x:
  "((\<lambda>y. M2cfun y c k l) has_derivative dM2cfun_x x c k l) (at x)"
proof -
  consider "k = (1::2) \<and> l = (1::2)" | "k = 1 \<and> l = 2" | "k = 2 \<and> l = 1" | "k = 2 \<and> l = 2"
    using exhaust_2[of k] exhaust_2[of l] by blast
  thus ?thesis
  proof cases
    case 1
    have F: "((\<lambda>y. M11_moment y c) has_derivative (\<lambda>h. d_M11_moment_x x c h)) (at x)"
      by (rule has_derivative_M11_moment_x)
    have eqn: "(\<lambda>y. M2cfun y c k l) = (\<lambda>y. M11_moment y c)"
      using 1 by (simp add: fun_eq_iff M2cfun_eq_M11_moment)
    have dEq: "dM2cfun_x x c k l = (\<lambda>h. d_M11_moment_x x c h)"
      using 1 by (simp add: dM2cfun_x_def)
    show ?thesis unfolding eqn dEq by (rule F)
  next
    case 2
    have F: "((\<lambda>y. M12_moment y c) has_derivative (\<lambda>h. d_M12_moment_x x c h)) (at x)"
      by (rule has_derivative_M12_moment_x)
    have eqn: "(\<lambda>y. M2cfun y c k l) = (\<lambda>y. M12_moment y c)"
      using 2 by (simp add: fun_eq_iff M2cfun_eq_M12_moment)
    have dEq: "dM2cfun_x x c k l = (\<lambda>h. d_M12_moment_x x c h)"
      using 2 by (simp add: dM2cfun_x_def)
    show ?thesis unfolding eqn dEq by (rule F)
  next
    case 3
    have F: "((\<lambda>y. M12_moment y c) has_derivative (\<lambda>h. d_M12_moment_x x c h)) (at x)"
      by (rule has_derivative_M12_moment_x)
    have eqn: "(\<lambda>y. M2cfun y c k l) = (\<lambda>y. M12_moment y c)"
      using 3 by (simp add: fun_eq_iff M2cfun_eq_M12_moment')
    have dEq: "dM2cfun_x x c k l = (\<lambda>h. d_M12_moment_x x c h)"
      using 3 by (simp add: dM2cfun_x_def)
    show ?thesis unfolding eqn dEq by (rule F)
  next
    case 4
    have F: "((\<lambda>y. M22_moment y c) has_derivative (\<lambda>h. d_M22_moment_x x c h)) (at x)"
      by (rule has_derivative_M22_moment_x)
    have eqn: "(\<lambda>y. M2cfun y c k l) = (\<lambda>y. M22_moment y c)"
      using 4 by (simp add: fun_eq_iff M2cfun_eq_M22_moment)
    have dEq: "dM2cfun_x x c k l = (\<lambda>h. d_M22_moment_x x c h)"
      using 4 by (simp add: dM2cfun_x_def)
    show ?thesis unfolding eqn dEq by (rule F)
  qed
qed

subsection \<open>Uniform perp-slot values\<close>

lemma dMcfun_x_perp:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "dMcfun_x x c k (slot m v) = of_real (vec_nth v k) * phase c x m"
proof -
  consider "k = (1::2)" | "k = 2" using exhaust_2 by blast
  thus ?thesis
    by cases (simp_all add: dMcfun_x_def d_M1_moment_x_perp[OF perp] d_M2_moment_x_perp[OF perp])
qed

lemma dM2cfun_x_perp:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "dM2cfun_x x c k l (slot m v)
       = of_real (vec_nth v k * vec_nth (vec_nth x m) l
                + vec_nth (vec_nth x m) k * vec_nth v l) * phase c x m"
proof -
  consider "k = (1::2) \<and> l = (1::2)" | "k = 1 \<and> l = 2" | "k = 2 \<and> l = 1" | "k = 2 \<and> l = 2"
    using exhaust_2[of k] exhaust_2[of l] by blast
  thus ?thesis
    by cases (simp_all add: dM2cfun_x_def d_M11_moment_x_perp[OF perp]
        d_M12_moment_x_perp[OF perp] d_M22_moment_x_perp[OF perp] dw_M12_def algebra_simps)
qed

subsection \<open>Block 1: the pattern value \<open>V = |A|\<^sup>2\<close>\<close>

lemma has_derivative_Uc_x:
  "((\<lambda>y. U_cart (\<lambda>c. c) (\<lambda>_. 1) y c) has_derivative
      (\<lambda>h. 2 * (Re (Afun x c) * Re (d_A_moment_x x c h)
              + Im (Afun x c) * Im (d_A_moment_x x c h)))) (at x)"
proof -
  have ReA: "((\<lambda>y. Re (Afun y c)) has_derivative (\<lambda>h. Re (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Afun_x])
  have ImA: "((\<lambda>y. Im (Afun y c)) has_derivative (\<lambda>h. Im (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Afun_x])
  have sq: "((\<lambda>y. (Re (Afun y c))\<^sup>2 + (Im (Afun y c))\<^sup>2) has_derivative
      (\<lambda>h. 2 * Re (Afun x c) * Re (d_A_moment_x x c h)
         + 2 * Im (Afun x c) * Im (d_A_moment_x x c h))) (at x)"
    unfolding power2_eq_square
    by (rule has_derivative_eq_rhs[OF has_derivative_add[OF
          has_derivative_mult[OF ReA ReA] has_derivative_mult[OF ImA ImA]]])
       (simp add: fun_eq_iff algebra_simps)
  have fun_eq: "(\<lambda>y. U_cart (\<lambda>c. c) (\<lambda>_. 1) y c)
      = (\<lambda>y. (Re (Afun y c))\<^sup>2 + (Im (Afun y c))\<^sup>2)"
    by (rule ext) (simp add: U_cart_def A_cart_eq_Afun cmod_power2)
  show ?thesis
    unfolding fun_eq
    by (rule has_derivative_eq_rhs[OF sq]) (simp add: fun_eq_iff algebra_simps)
qed

lemma Uc_perp_slot_deriv:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "2 * (Re (Afun x c) * Re (d_A_moment_x x c (slot m v))
            + Im (Afun x c) * Im (d_A_moment_x x c (slot m v))) = 0"
  by (simp add: d_A_moment_x_perp[OF perp])

subsection \<open>Block 2: the \<open>c\<close>-gradient components\<close>

lemma has_derivative_gradUc_comp_x:
  "((\<lambda>y. vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) i) has_derivative
      (\<lambda>h. 2 * (Re (d_A_moment_x x c h) * Im (Mcfun x c i)
              + Re (Afun x c) * Im (dMcfun_x x c i h)
              - (Im (d_A_moment_x x c h) * Re (Mcfun x c i)
              + Im (Afun x c) * Re (dMcfun_x x c i h))))) (at x)"
proof -
  have ReA: "((\<lambda>y. Re (Afun y c)) has_derivative (\<lambda>h. Re (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Afun_x])
  have ImA: "((\<lambda>y. Im (Afun y c)) has_derivative (\<lambda>h. Im (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Afun_x])
  have ReM: "((\<lambda>y. Re (Mcfun y c i)) has_derivative (\<lambda>h. Re (dMcfun_x x c i h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Mcfun_x])
  have ImM: "((\<lambda>y. Im (Mcfun y c i)) has_derivative (\<lambda>h. Im (dMcfun_x x c i h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Mcfun_x])
  have core: "((\<lambda>y. 2 * (Re (Afun y c) * Im (Mcfun y c i) - Im (Afun y c) * Re (Mcfun y c i)))
      has_derivative
      (\<lambda>h. 2 * (Re (d_A_moment_x x c h) * Im (Mcfun x c i)
              + Re (Afun x c) * Im (dMcfun_x x c i h)
              - (Im (d_A_moment_x x c h) * Re (Mcfun x c i)
              + Im (Afun x c) * Re (dMcfun_x x c i h))))) (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult_right[OF has_derivative_diff[OF
          has_derivative_mult[OF ReA ImM] has_derivative_mult[OF ImA ReM]]]])
       (simp add: fun_eq_iff algebra_simps)
  have fun_eq: "(\<lambda>y. vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) i)
      = (\<lambda>y. 2 * (Re (Afun y c) * Im (Mcfun y c i) - Im (Afun y c) * Re (Mcfun y c i)))"
    by (rule ext) (simp add: gradU_c_field)
  show ?thesis unfolding fun_eq by (rule core)
qed

lemma gradUc_comp_perp_slot_deriv:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "2 * (Re (d_A_moment_x x c (slot m v)) * Im (Mcfun x c i)
            + Re (Afun x c) * Im (dMcfun_x x c i (slot m v))
            - (Im (d_A_moment_x x c (slot m v)) * Re (Mcfun x c i)
            + Im (Afun x c) * Re (dMcfun_x x c i (slot m v))))
       = 2 * vec_nth v i * Im (cnj (Afun x c) * phase c x m)"
  by (simp add: d_A_moment_x_perp[OF perp] dMcfun_x_perp[OF perp] algebra_simps)

subsection \<open>Block 3: the \<open>Hcmat\<close> entries\<close>

lemma has_derivative_Hcmat_entry_x:
  "((\<lambda>y. vec_nth (vec_nth (Hcmat y c) k) l) has_derivative
      (\<lambda>h. 2 * ((Re (dMcfun_x x c l h) * Re (Mcfun x c k) + Im (dMcfun_x x c l h) * Im (Mcfun x c k)
               + (Re (Mcfun x c l) * Re (dMcfun_x x c k h) + Im (Mcfun x c l) * Im (dMcfun_x x c k h)))
              - ((Re (d_A_moment_x x c h) * Re (M2cfun x c k l) + Im (d_A_moment_x x c h) * Im (M2cfun x c k l))
               + (Re (Afun x c) * Re (dM2cfun_x x c k l h) + Im (Afun x c) * Im (dM2cfun_x x c k l h)))))) (at x)"
proof -
  have ReA: "((\<lambda>y. Re (Afun y c)) has_derivative (\<lambda>h. Re (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Afun_x])
  have ImA: "((\<lambda>y. Im (Afun y c)) has_derivative (\<lambda>h. Im (d_A_moment_x x c h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Afun_x])
  have ReMk: "((\<lambda>y. Re (Mcfun y c k)) has_derivative (\<lambda>h. Re (dMcfun_x x c k h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Mcfun_x])
  have ImMk: "((\<lambda>y. Im (Mcfun y c k)) has_derivative (\<lambda>h. Im (dMcfun_x x c k h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Mcfun_x])
  have ReMl: "((\<lambda>y. Re (Mcfun y c l)) has_derivative (\<lambda>h. Re (dMcfun_x x c l h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_Mcfun_x])
  have ImMl: "((\<lambda>y. Im (Mcfun y c l)) has_derivative (\<lambda>h. Im (dMcfun_x x c l h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_Mcfun_x])
  have ReM2: "((\<lambda>y. Re (M2cfun y c k l)) has_derivative (\<lambda>h. Re (dM2cfun_x x c k l h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Re has_derivative_M2cfun_x])
  have ImM2: "((\<lambda>y. Im (M2cfun y c k l)) has_derivative (\<lambda>h. Im (dM2cfun_x x c k l h))) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_Im has_derivative_M2cfun_x])
  have core: "((\<lambda>y. 2 * ((Re (Mcfun y c l) * Re (Mcfun y c k) + Im (Mcfun y c l) * Im (Mcfun y c k))
                       - (Re (Afun y c) * Re (M2cfun y c k l) + Im (Afun y c) * Im (M2cfun y c k l))))
      has_derivative
      (\<lambda>h. 2 * ((Re (dMcfun_x x c l h) * Re (Mcfun x c k) + Im (dMcfun_x x c l h) * Im (Mcfun x c k)
               + (Re (Mcfun x c l) * Re (dMcfun_x x c k h) + Im (Mcfun x c l) * Im (dMcfun_x x c k h)))
              - ((Re (d_A_moment_x x c h) * Re (M2cfun x c k l) + Im (d_A_moment_x x c h) * Im (M2cfun x c k l))
               + (Re (Afun x c) * Re (dM2cfun_x x c k l h) + Im (Afun x c) * Im (dM2cfun_x x c k l h)))))) (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult_right[OF has_derivative_diff[OF
          has_derivative_add[OF has_derivative_mult[OF ReMl ReMk] has_derivative_mult[OF ImMl ImMk]]
          has_derivative_add[OF has_derivative_mult[OF ReA ReM2] has_derivative_mult[OF ImA ImM2]]]]])
       (simp add: fun_eq_iff algebra_simps)
  have fun_eq: "(\<lambda>y. vec_nth (vec_nth (Hcmat y c) k) l)
      = (\<lambda>y. 2 * ((Re (Mcfun y c l) * Re (Mcfun y c k) + Im (Mcfun y c l) * Im (Mcfun y c k))
              - (Re (Afun y c) * Re (M2cfun y c k l) + Im (Afun y c) * Im (M2cfun y c k l))))"
    by (rule ext) (simp add: Hcmat_entry_eq algebra_simps)
  show ?thesis unfolding fun_eq by (rule core)
qed

lemma Hcmat_entry_perp_slot_deriv:
  fixes c v :: "real^2"
  assumes perp: "c \<bullet> v = 0"
  shows "2 * ((Re (dMcfun_x x c l (slot m v)) * Re (Mcfun x c k)
             + Im (dMcfun_x x c l (slot m v)) * Im (Mcfun x c k)
             + (Re (Mcfun x c l) * Re (dMcfun_x x c k (slot m v))
             + Im (Mcfun x c l) * Im (dMcfun_x x c k (slot m v))))
            - ((Re (d_A_moment_x x c (slot m v)) * Re (M2cfun x c k l)
             + Im (d_A_moment_x x c (slot m v)) * Im (M2cfun x c k l))
             + (Re (Afun x c) * Re (dM2cfun_x x c k l (slot m v))
             + Im (Afun x c) * Im (dM2cfun_x x c k l (slot m v)))))
       = 2 * (vec_nth v l * Re (cnj (phase c x m) * Mcfun x c k)
            + vec_nth v k * Re (cnj (Mcfun x c l) * phase c x m)
            - (vec_nth v k * vec_nth (vec_nth x m) l
             + vec_nth (vec_nth x m) k * vec_nth v l) * Re (cnj (Afun x c) * phase c x m))"
  by (simp add: d_A_moment_x_perp[OF perp] dMcfun_x_perp[OF perp] dM2cfun_x_perp[OF perp]
      algebra_simps)


section \<open>Assembling the HessU-entry x-derivative (fixed \<omega>) from the three blocks\<close>

text \<open>@{thm HessU_dip_entry_moments} expresses \<open>HessU(\<cdot>,\<omega>)$k$l\<close> as a fixed-\<omega> linear
  combination of the three \<open>x\<close>-varying blocks \<open>V\<close>, \<open>gradcV\<close>, \<open>Hcmat\<close> (everything else
  --- \<open>Dcvec_dip\<close>, \<open>D2cvec_dip\<close>, \<open>gain_dip\<close>, the \<open>gdip\<close> jets --- depends only on \<open>\<omega>\<close>,
  hence is CONSTANT in \<open>x\<close>).  This theory assembles the \<open>x\<close>-derivative of the entry
  from the three already-proven block derivatives, then specialises to a
  perpendicular slot direction.\<close>

subsection \<open>Named block-derivative abbreviations (repackaging the proven block facts)\<close>

definition dV_x :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "dV_x x c h = 2 * (Re (Afun x c) * Re (d_A_moment_x x c h)
                    + Im (Afun x c) * Im (d_A_moment_x x c h))"

definition dgradcV_x :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "dgradcV_x x c i h = 2 * (Re (d_A_moment_x x c h) * Im (Mcfun x c i)
                          + Re (Afun x c) * Im (dMcfun_x x c i h)
                          - (Im (d_A_moment_x x c h) * Re (Mcfun x c i)
                          + Im (Afun x c) * Re (dMcfun_x x c i h)))"

definition dHcmat_x :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> 2 \<Rightarrow> 2 \<Rightarrow> (real^2)^'n \<Rightarrow> real" where
  "dHcmat_x x c p q h = 2 * ((Re (dMcfun_x x c q h) * Re (Mcfun x c p)
               + Im (dMcfun_x x c q h) * Im (Mcfun x c p)
               + (Re (Mcfun x c q) * Re (dMcfun_x x c p h) + Im (Mcfun x c q) * Im (dMcfun_x x c p h)))
              - ((Re (d_A_moment_x x c h) * Re (M2cfun x c p q) + Im (d_A_moment_x x c h) * Im (M2cfun x c p q))
               + (Re (Afun x c) * Re (dM2cfun_x x c p q h) + Im (Afun x c) * Im (dM2cfun_x x c p q h))))"

lemma has_derivative_Uc_x': "((\<lambda>y. U_cart (\<lambda>c. c) (\<lambda>_. 1) y c) has_derivative dV_x x c) (at x)"
  unfolding dV_x_def by (rule has_derivative_Uc_x)

lemma has_derivative_gradUc_comp_x':
  "((\<lambda>y. vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) i) has_derivative dgradcV_x x c i) (at x)"
  unfolding dgradcV_x_def by (rule has_derivative_gradUc_comp_x)

lemma has_derivative_Hcmat_entry_x':
  "((\<lambda>y. vec_nth (vec_nth (Hcmat y c) p) q) has_derivative dHcmat_x x c p q) (at x)"
  unfolding dHcmat_x_def by (rule has_derivative_Hcmat_entry_x)

subsection \<open>Perp-slot values of the block-derivative names\<close>

lemma dV_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "dV_x x c (slot m v) = 0"
  unfolding dV_x_def using Uc_perp_slot_deriv[OF assms] .

lemma dgradcV_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "dgradcV_x x c i (slot m v) = 2 * vec_nth v i * Im (cnj (Afun x c) * phase c x m)"
  unfolding dgradcV_x_def using gradUc_comp_perp_slot_deriv[OF assms] .

lemma dHcmat_x_perp:
  fixes c v :: "real^2"
  assumes "c \<bullet> v = 0"
  shows "dHcmat_x x c p q (slot m v)
       = 2 * (vec_nth v q * Re (cnj (phase c x m) * Mcfun x c p)
            + vec_nth v p * Re (cnj (Mcfun x c q) * phase c x m)
            - (vec_nth v p * vec_nth (vec_nth x m) q
             + vec_nth (vec_nth x m) p * vec_nth v q) * Re (cnj (Afun x c) * phase c x m))"
  unfolding dHcmat_x_def using Hcmat_entry_perp_slot_deriv[OF assms] .

subsection \<open>A fixed vector paired with the \<open>gradcV\<close> block\<close>

lemma has_derivative_gradcV_inner_x:
  fixes w c :: "real^2"
  shows "((\<lambda>y. w \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y c) has_derivative
           (\<lambda>h. vec_nth w 1 * dgradcV_x x c 1 h + vec_nth w 2 * dgradcV_x x c 2 h)) (at x)"
proof -
  have d1: "((\<lambda>y. vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) 1) has_derivative dgradcV_x x c 1) (at x)"
    by (rule has_derivative_gradUc_comp_x')
  have d2: "((\<lambda>y. vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) 2) has_derivative dgradcV_x x c 2) (at x)"
    by (rule has_derivative_gradUc_comp_x')
  have core: "((\<lambda>y. vec_nth w 1 * vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) 1
               + vec_nth w 2 * vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) 2)
       has_derivative (\<lambda>h. vec_nth w 1 * dgradcV_x x c 1 h + vec_nth w 2 * dgradcV_x x c 2 h)) (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_add[OF
          has_derivative_mult[OF has_derivative_const d1]
          has_derivative_mult[OF has_derivative_const d2]]])
       (simp add: fun_eq_iff algebra_simps)
  have eq: "(\<lambda>y. w \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y c)
      = (\<lambda>y. vec_nth w 1 * vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) 1
           + vec_nth w 2 * vec_nth (gradU (\<lambda>c. c) (\<lambda>_. 1) y c) 2)"
    by (rule ext) (simp add: inner_vec_def sum_2)
  show ?thesis unfolding eq by (rule core)
qed

subsection \<open>Two fixed vectors paired with the \<open>Hcmat\<close> block\<close>

lemma has_derivative_Hcmat_bilinear_x:
  fixes w1 w2 c :: "real^2"
  shows "((\<lambda>y. w1 \<bullet> (Hcmat y c *v w2)) has_derivative
           (\<lambda>h. vec_nth w1 1 * vec_nth w2 1 * dHcmat_x x c 1 1 h
              + vec_nth w1 1 * vec_nth w2 2 * dHcmat_x x c 1 2 h
              + vec_nth w1 2 * vec_nth w2 1 * dHcmat_x x c 2 1 h
              + vec_nth w1 2 * vec_nth w2 2 * dHcmat_x x c 2 2 h)) (at x)"
proof -
  have d11: "((\<lambda>y. vec_nth (vec_nth (Hcmat y c) 1) 1) has_derivative dHcmat_x x c 1 1) (at x)"
    by (rule has_derivative_Hcmat_entry_x')
  have d12: "((\<lambda>y. vec_nth (vec_nth (Hcmat y c) 1) 2) has_derivative dHcmat_x x c 1 2) (at x)"
    by (rule has_derivative_Hcmat_entry_x')
  have d21: "((\<lambda>y. vec_nth (vec_nth (Hcmat y c) 2) 1) has_derivative dHcmat_x x c 2 1) (at x)"
    by (rule has_derivative_Hcmat_entry_x')
  have d22: "((\<lambda>y. vec_nth (vec_nth (Hcmat y c) 2) 2) has_derivative dHcmat_x x c 2 2) (at x)"
    by (rule has_derivative_Hcmat_entry_x')
  have core: "((\<lambda>y. vec_nth w1 1 * vec_nth w2 1 * vec_nth (vec_nth (Hcmat y c) 1) 1
               + vec_nth w1 1 * vec_nth w2 2 * vec_nth (vec_nth (Hcmat y c) 1) 2
               + vec_nth w1 2 * vec_nth w2 1 * vec_nth (vec_nth (Hcmat y c) 2) 1
               + vec_nth w1 2 * vec_nth w2 2 * vec_nth (vec_nth (Hcmat y c) 2) 2)
       has_derivative
       (\<lambda>h. vec_nth w1 1 * vec_nth w2 1 * dHcmat_x x c 1 1 h
          + vec_nth w1 1 * vec_nth w2 2 * dHcmat_x x c 1 2 h
          + vec_nth w1 2 * vec_nth w2 1 * dHcmat_x x c 2 1 h
          + vec_nth w1 2 * vec_nth w2 2 * dHcmat_x x c 2 2 h)) (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_add[OF has_derivative_add[OF has_derivative_add[OF
          has_derivative_mult[OF has_derivative_const d11]
          has_derivative_mult[OF has_derivative_const d12]]
          has_derivative_mult[OF has_derivative_const d21]]
          has_derivative_mult[OF has_derivative_const d22]]])
       (simp add: fun_eq_iff algebra_simps)
  have eq: "(\<lambda>y. w1 \<bullet> (Hcmat y c *v w2))
      = (\<lambda>y. vec_nth w1 1 * vec_nth w2 1 * vec_nth (vec_nth (Hcmat y c) 1) 1
           + vec_nth w1 1 * vec_nth w2 2 * vec_nth (vec_nth (Hcmat y c) 1) 2
           + vec_nth w1 2 * vec_nth w2 1 * vec_nth (vec_nth (Hcmat y c) 2) 1
           + vec_nth w1 2 * vec_nth w2 2 * vec_nth (vec_nth (Hcmat y c) 2) 2)"
    by (rule ext) (simp add: inner_vec_def matrix_vector_mult_def sum_2 algebra_simps)
  show ?thesis unfolding eq by (rule core)
qed

subsection \<open>Assembly: the Hessian entry's \<open>x\<close>-derivative (fixed \<open>\<omega>\<close>)\<close>


theorem has_derivative_HessU_dip_entry_x:
  fixes k l :: 2
  shows "((\<lambda>y. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ k $ l) has_derivative
      (\<lambda>h. gain_dip \<omega> *
             ((vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 1 h
             + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 2 h
             + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 1 h
             + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 2 h)
             + (vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
              + vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h))
         + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1) 1)
             * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
              + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)
         + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1) 1)
             * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
              + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)
         + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1) 1)) (at \<omega>)
             (axis l 1) * dV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) (at x)"
proof -
  have hcbil: "((\<lambda>y. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> (Hcmat y (cvec_dip \<omega>0 \<omega>s \<omega>) *v Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)))
       has_derivative
       (\<lambda>h. vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
              * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 1 h
          + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
              * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 2 h
          + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
              * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 1 h
          + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
              * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 2 h)) (at x)"
    by (rule has_derivative_Hcmat_bilinear_x)
  have gk: "((\<lambda>y. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative
       (\<lambda>h. vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
          + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)) (at x)"
    by (rule has_derivative_gradcV_inner_x)
  have gl: "((\<lambda>y. Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative
       (\<lambda>h. vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
          + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)) (at x)"
    by (rule has_derivative_gradcV_inner_x)
  have dk: "((\<lambda>y. D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>))
       has_derivative
       (\<lambda>h. vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
          + vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)) (at x)"
    by (rule has_derivative_gradcV_inner_x)
  have vv: "((\<lambda>y. U_cart (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>)) has_derivative
       dV_x x (cvec_dip \<omega>0 \<omega>s \<omega>)) (at x)"
    by (rule has_derivative_Uc_x')
  have part1: "((\<lambda>y. gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                    \<bullet> (Hcmat y (cvec_dip \<omega>0 \<omega>s \<omega>) *v Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))
                + D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>)))
       has_derivative
       (\<lambda>h. gain_dip \<omega> *
              ((vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
                   * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 1 h
               + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
                   * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 2 h
               + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
                   * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 1 h
               + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
                   * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 2 h)
              + (vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
               + vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h))))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const has_derivative_add[OF hcbil dk]]])
       (simp add: fun_eq_iff algebra_simps)
  have part2: "((\<lambda>y. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1) 1)
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>)))
       has_derivative
       (\<lambda>h. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1) 1)
              * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
               + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const gk]])
       (simp add: fun_eq_iff)
  have part3: "((\<lambda>y. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1) 1)
                    * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>)))
       has_derivative
       (\<lambda>h. frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1) 1)
              * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 h
               + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 h)))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const gl]])
       (simp add: fun_eq_iff)
  have part4: "((\<lambda>y. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1) 1))
                    (at \<omega>) (axis l 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>))
       has_derivative
       (\<lambda>h. frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1) 1)) (at \<omega>)
              (axis l 1) * dV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const vv]])
       (simp add: fun_eq_iff)
  have fun_eq: "(\<lambda>y. HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega> $ k $ l)
      = (\<lambda>y. gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)
                  \<bullet> (Hcmat y (cvec_dip \<omega>0 \<omega>s \<omega>) *v Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1))
              + D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>))
           + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1) 1)
               * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>))
           + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1) 1)
               * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1) \<bullet> gradU (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>))
           + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1) 1)) (at \<omega>)
               (axis l 1) * U_cart (\<lambda>c. c) (\<lambda>_. 1) y (cvec_dip \<omega>0 \<omega>s \<omega>))"
    by (rule ext) (simp add: HessU_dip_entry_moments algebra_simps)
  show ?thesis
    unfolding fun_eq
    by (rule has_derivative_eq_rhs[OF has_derivative_add[OF has_derivative_add[OF
          has_derivative_add[OF part1 part2] part3] part4]])
       (simp add: fun_eq_iff algebra_simps)
qed

subsection \<open>Perp-slot corollary: the Hessian entry's derivative in a perpendicular slot\<close>

text \<open>The Fr\'echet derivative of the entry, evaluated at \<open>h = slot m v\<close> with
  \<open>c \<bullet> v = 0\<close>: substitute the three block perp-slot values
  (@{thm dV_x_perp}, @{thm dgradcV_x_perp}, @{thm dHcmat_x_perp}) into the general
  formula from @{thm has_derivative_HessU_dip_entry_x}.\<close>

theorem HessU_dip_entry_perp_slot_value:
  fixes k l :: 2 and m :: "'n::finite" and v \<omega>0 \<omega>s :: "real^2"
    and x :: "(real^2)^'n"
  assumes perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) k) l) (at x) (slot m v)
       = gain_dip \<omega> *
             (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 1 (slot m v)
             + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 2 (slot m v)
             + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 1 (slot m v)
             + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2
                  * dHcmat_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 2 (slot m v)
             + (vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 1
                  * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 (slot m v)
              + vec_nth (D2cvec_dip \<omega>0 \<omega>s \<omega> (axis k 1) (axis l 1)) 2
                  * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 (slot m v)))
         + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis l 1) 1)
             * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 (slot m v)
              + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis k 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 (slot m v))
         + frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis k 1) 1)
             * (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 1 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 1 (slot m v)
              + vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis l 1)) 2 * dgradcV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) 2 (slot m v))
         + frechet_derivative (\<lambda>\<eta>. frechet_derivative gdip (at (vec_nth \<eta> 1)) (vec_nth (axis k 1) 1)) (at \<omega>)
             (axis l 1) * dV_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v)"
  by (rule fun_cong[OF frechet_derivative_at[OF has_derivative_HessU_dip_entry_x, symmetric]])


section \<open>The G11 quotient-rule derivative and the Delta_ij determinant identity\<close>

text \<open>The paper's \<open>G\<^sub>1\<^sub>1 := \<Phi>\<^sub>3/H\<^sub>1\<^sub>1 = H\<^sub>2\<^sub>2 - H\<^sub>1\<^sub>2\<^sup>2/H\<^sub>1\<^sub>1\<close> (\<open>prop:vpair11\<close>) and the rank-3
  criterion's \<open>\<Delta>\<^sub>i\<^sub>j := det \<partial>(\<Phi>\<^sub>2,G\<^sub>1\<^sub>1)/\<partial>(v\<^sub>i,v\<^sub>j)\<close>, in INVARIANT (gauge-free) form: \<open>v\<^sub>i\<close>
  is the perpendicular slot direction \<open>slot i (perp2 c)\<close> for triple element \<open>i\<close>.\<close>

subsection \<open>Phi_2's perp-slot value, in \<open>frechet_derivative\<close> form\<close>

lemma Phi2_perp_slot_value:
  fixes m :: "'n::finite" and v \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x) (slot m v)
       = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v)
           * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
proof -
  have hd2: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
       (\<lambda>h. vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_gradU_dip_x_explicit])
  have val: "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x) (slot m v)
      = vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 2"
    by (rule fun_cong[OF frechet_derivative_at[OF hd2, symmetric]])
  show ?thesis
    unfolding val
    using arg_cong[where f = "\<lambda>V. vec_nth V 2", OF gradU_dip_xderiv_perp_slot[OF perp]]
    by simp
qed

subsection \<open>G11: the quotient-rule \<open>x\<close>-derivative (fixed \<open>\<omega>\<close>)\<close>

definition G11 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "G11 x \<omega> \<omega>0 \<omega>s = vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
       - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
         / vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1"

theorem has_derivative_G11_x:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes h11nz: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1 \<noteq> 0"
  shows "((\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) has_derivative
      (\<lambda>h. frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) h
         - ((2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h)
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
            - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) h)
           / (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1))) (at x)"
proof -
  have h22: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 2 and l = 2], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h12: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 1 and l = 2], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h11: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 1 and l = 1], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h12sq: "((\<lambda>y. (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2)\<^sup>2) has_derivative
       (\<lambda>h. 2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h))
       (at x)"
    unfolding power2_eq_square
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF h12 h12]]) (simp add: fun_eq_iff algebra_simps)
  have hdiv: "((\<lambda>y. (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2)\<^sup>2
                   / vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1)
       has_derivative
       (\<lambda>h. ((2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h)
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
            - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) h)
           / (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1))) (at x)"
    by (rule has_derivative_divide'[OF h12sq h11 h11nz])
  show ?thesis
    unfolding G11_def
    by (rule has_derivative_diff[OF h22 hdiv])
qed

subsection \<open>G11's perp-slot value (via the Hessian-entry perp-slot values)\<close>

text \<open>The quotient-rule value of \<open>G\<^sub>1\<^sub>1\<close>'s derivative at a perpendicular slot, expressed
  through \<open>H\<^sub>2\<^sub>2\<close>/\<open>H\<^sub>1\<^sub>2\<close>/\<open>H\<^sub>1\<^sub>1\<close>'s ALREADY-CHARACTERISED perp-slot derivatives
  (@{thm HessU_dip_entry_perp_slot_value}) --- kept PACKAGED (in \<open>frechet_derivative\<close>
  form) rather than force-flattening into raw \<open>Re\<close>/\<open>Im\<close> arithmetic, which the paper's
  own \<open>H\<close>-entry formulas already show is intrinsically multi-term.\<close>

theorem G11_perp_slot_value:
  fixes m :: "'n::finite" and v \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes h11nz: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1 \<noteq> 0"
    and perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot m v)
       = frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) (slot m v)
       - ((2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x)
                  (slot m v))
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
            - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x)
                  (slot m v))
           / (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1)"
  by (rule fun_cong[OF frechet_derivative_at[OF has_derivative_G11_x[OF h11nz], symmetric]])

subsection \<open>The Delta_ij determinant, invariantly (perpendicular-slot directions at two triple elements)\<close>

text \<open>\<open>\<Delta>\<^sub>i\<^sub>j := det \<partial>(\<Phi>\<^sub>2,G\<^sub>1\<^sub>1)/\<partial>(v_i,v_j)\<close> (\<open>prop:vpair11\<close>), with \<open>v_i\<close> the
  perpendicular slot direction for triple element \<open>i\<close> (i.e. \<open>slot i (perp2 c)\<close>).\<close>

definition Delta_ij :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Delta_ij x \<omega> \<omega>0 \<omega>s i j =
     frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
         (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       * frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
   - frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
         (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       * frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"

text \<open>The \<open>\<Delta>\<^sub>i\<^sub>j\<close> identity: the \<open>\<Phi>\<^sub>2\<close>-factors collapse to their clean closed form
  (@{thm Phi2_perp_slot_value}); the \<open>G\<^sub>1\<^sub>1\<close>-factors are the already-characterised
  quotient-rule values (@{thm G11_perp_slot_value}) --- this is \<open>prop:vpair11\<close>'s
  determinant identity in fully invariant (gauge-free) form.  Assumes ONLY the
  cofactor \<open>H\<^sub>1\<^sub>1 \<noteq> 0\<close> at the base point (\<open>prop:vpair11\<close>'s own hypothesis).\<close>

theorem Delta_ij_identity:
  fixes i j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes h11nz: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1 \<noteq> 0"
  shows "Delta_ij x \<omega> \<omega>0 \<omega>s i j
       = (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
            * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x i))
           * frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       - (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
            * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x j))
           * frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
proof -
  have perpi: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  show ?thesis
    unfolding Delta_ij_def
    by (simp add: Phi2_perp_slot_value[OF perpi])
qed


section \<open>The rank-3 criterion (cor:vpair11), invariantly\<close>

text \<open>The paper's block-triangular argument needs \<open>\<Phi>\<^sub>1\<close> INDEPENDENT of every v-slot
  ---a fact of their SPECIFIC omega-parametrization, NOT automatic for our
  \<open>(sin\<theta>cos\<phi>,...)\<close> angular coordinates: \<open>gradU_dip_xderiv_perp_slot\<close> gives BOTH
  components \<open>j=1,2\<close> the SAME nonzero shape \<open>2g\<^sub>0(\<gamma>\<^sub>j\<bullet>v)W_m\<close>, so the plain component
  \<open>gradU$1\<close> does NOT vanish on a v-slot in general.  The fix: replace the omega-basis
  vector \<open>axis 1 1\<close> by \<open>e_par\<close>, the (unique, given \<open>det(matrix(Dcvec_dip))\<noteq>0\<close>) omega
  DIRECTION whose PUSHFORWARD under \<open>Dcvec_dip\<close> is \<open>c\<close> itself.  Then
  \<open>\<Phi>_par := gradU \<bullet> e_par\<close> plays \<open>\<Phi>\<^sub>1\<close>'s role EXACTLY: its v-slot derivative is
  \<open>2g\<^sub>0 W_m (Dcvec_dip(e_par)\<bullet>v) = 2g\<^sub>0 W_m (c\<bullet>v) = 0\<close> for \<open>v = perp2 c\<close>, by
  CONSTRUCTION --- this is the invariant analogue of the paper's own omega-gauge
  choice, not an assumption.\<close>

subsection \<open>The omega-direction \<open>e\_par\<close> pushing forward to \<open>c\<close>\<close>

definition e_par :: "real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "e_par \<omega>0 \<omega>s \<omega> = inv_into UNIV ((*v) (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>))) (cvec_dip \<omega>0 \<omega>s \<omega>)"

lemma Dcvec_dip_e_par:
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Dcvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) = cvec_dip \<omega>0 \<omega>s \<omega>"
proof -
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have decomp: "\<And>h::real^2. h = vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix h :: "real^2" and i :: 2
    show "vec_nth h i = vec_nth (vec_nth h 1 *\<^sub>R axis 1 1 + vec_nth h 2 *\<^sub>R axis 2 1) i"
      using exhaust_2[of i] by (auto simp: axis_def)
  qed
  have mv: "matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h = Dcvec_dip \<omega>0 \<omega>s \<omega> h" for h :: "real^2"
  proof -
    have expand: "matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h
        = vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
    proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
      fix i :: 2
      show "vec_nth (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v h) i
          = vec_nth (vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
                   + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)) i"
        by (simp add: matrix_def matrix_vector_mult_def sum_2 algebra_simps)
    qed
    have "Dcvec_dip \<omega>0 \<omega>s \<omega> h
        = vec_nth h 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) + vec_nth h 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
      using decomp[of h] linear_add[OF lin] linear_cmul[OF lin] by metis
    with expand show ?thesis by simp
  qed
  have bij: "bij ((*v) (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)))"
    by (rule bij_matrix_vector_mult[OF detnz])
  have "matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>) *v e_par \<omega>0 \<omega>s \<omega> = cvec_dip \<omega>0 \<omega>s \<omega>"
    unfolding e_par_def by (rule surj_f_inv_f[OF bij_is_surj[OF bij]])
  thus ?thesis
    using mv by simp
qed

subsection \<open>\<open>\<Phi>_par\<close>: the omega-direction of the gradient that pushes forward to \<open>c\<close>\<close>

definition Phi_par :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "Phi_par x \<omega> \<omega>0 \<omega>s = gradU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega> \<bullet> e_par \<omega>0 \<omega>s \<omega>"

text \<open>A fixed vector paired with the FULL \<open>gradU\<close> vector (not just \<open>gradcV\<close>): the
  same 2-component-sum pattern as \<open>has_derivative_gradcV_inner_x\<close>, but composing
  with @{thm has_derivative_gradU_dip_x_explicit} instead of the c-gradient block.\<close>

lemma has_derivative_gradU_inner_x:
  fixes w \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n::finite"
  shows "((\<lambda>y. w \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
      (\<lambda>h. vec_nth w 1
             * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1
         + vec_nth w 2
             * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
proof -
  have d1: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) has_derivative
       (\<lambda>h. vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_gradU_dip_x_explicit])
  have d2: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
       (\<lambda>h. vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_gradU_dip_x_explicit])
  have core: "((\<lambda>y. vec_nth w 1 * vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1
               + vec_nth w 2 * vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2)
       has_derivative
       (\<lambda>h. vec_nth w 1
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1
            + vec_nth w 2
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
      for y :: "(real^2)^'n"
    by (rule has_derivative_eq_rhs[OF has_derivative_add[OF
          has_derivative_mult[OF has_derivative_const d1]
          has_derivative_mult[OF has_derivative_const d2]]])
       (simp add: fun_eq_iff algebra_simps)
  have eq: "(\<lambda>y. w \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)
      = (\<lambda>y. vec_nth w 1 * vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1
           + vec_nth w 2 * vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2)"
    by (rule ext) (simp add: inner_vec_def sum_2)
  show ?thesis unfolding eq by (rule core)
qed

subsection \<open>The key lemma: \<open>\<Phi>_par\<close>'s perp-slot derivative vanishes\<close>

theorem Phi_par_perp_slot_zero:
  fixes m :: "'n::finite" and v \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m v) = 0"
proof -
  have hd: "((\<lambda>y. e_par \<omega>0 \<omega>s \<omega> \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1
            + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
    by (rule has_derivative_gradU_inner_x)
  have val: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m v)
      = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
          * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 1
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
          * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 2"
  proof -
    have eq: "(\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) = (\<lambda>y. e_par \<omega>0 \<omega>s \<omega> \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)"
      by (rule ext) (simp add: Phi_par_def inner_commute)
    show ?thesis
      unfolding eq
      by (rule fun_cong[OF frechet_derivative_at[OF hd, symmetric]])
  qed
  have j1: "vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 1
      = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
    using arg_cong[where f = "\<lambda>V. vec_nth V 1", OF gradU_dip_xderiv_perp_slot[OF perp]] by simp
  have j2: "vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
               (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
               (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
               (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m v))) 2
      = 2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v)
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
    using arg_cong[where f = "\<lambda>V. vec_nth V 2", OF gradU_dip_xderiv_perp_slot[OF perp]] by simp
  have lin: "linear (Dcvec_dip \<omega>0 \<omega>s \<omega>)"
    by (rule bounded_linear.linear[OF has_derivative_bounded_linear[OF has_derivative_cvec_dip]])
  have decomp: "e_par \<omega>0 \<omega>s \<omega>
      = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 *\<^sub>R axis 1 1 + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 *\<^sub>R axis 2 1"
  proof (rule Finite_Cartesian_Product.vec_eq_iff[THEN iffD2], intro allI)
    fix i :: 2
    show "vec_nth (e_par \<omega>0 \<omega>s \<omega>) i
        = vec_nth (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 *\<^sub>R axis 1 1
                 + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 *\<^sub>R axis 2 1) i"
      using exhaust_2[of i] by (auto simp: axis_def)
  qed
  have push: "Dcvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>)
      = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
      + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
  proof -
    have "Dcvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>)
        = Dcvec_dip \<omega>0 \<omega>s \<omega> (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 *\<^sub>R axis 1 1
                 + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 *\<^sub>R axis 2 1)"
      using decomp by simp
    also have "\<dots> = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1)
                   + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 *\<^sub>R Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1)"
      by (simp add: linear_add[OF lin] linear_cmul[OF lin])
    finally show ?thesis .
  qed
  have factor: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
              + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v)
      = Dcvec_dip \<omega>0 \<omega>s \<omega> (e_par \<omega>0 \<omega>s \<omega>) \<bullet> v"
    unfolding push by (simp add: inner_add_left)
  have regroup: "vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
        * (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
             * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))
      + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
        * (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v)
             * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m))
      = 2 * gain_dip \<omega>
          * (vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 1 1) \<bullet> v)
           + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> v))
          * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x m)"
    by (simp add: algebra_simps)
  show ?thesis
    unfolding val j1 j2 regroup factor
    using Dcvec_dip_e_par[OF detnz] perp
    by simp
qed


section \<open>The rank-3 criterion itself: the Jac3 determinant identity\<close>

text \<open>The paper's block-triangular reduction (cor:vpair11): given a direction U
  (any x-tangent direction, playing the role of the paper's u-slot direction),
  the Jacobian of \<open>(\<Phi>_par, \<Phi>2, G11)\<close> restricted to \<open>(U, slot_i(perp2 c),
  slot_j(perp2 c))\<close> is BLOCK TRIANGULAR since \<open>\<Phi>_par\<close>'s entries in columns 2,3
  vanish (@{thm Phi_par_perp_slot_zero}), so its determinant collapses to
  \<open>D\<Phi>_par(U) * Delta_ij(i,j)\<close> via cofactor expansion along row 1 --- reusing
  the existing \<open>det3\<close> primitive.\<close>

definition Jac3 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2
      \<Rightarrow> (real^2)^'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Jac3 x \<omega> \<omega>0 \<omega>s U i j =
     det3
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) U)
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x) U)
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) U)
       (frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. G11 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))"

theorem Jac3_identity:
  fixes i j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x U :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Jac3 x \<omega> \<omega>0 \<omega>s U i j
       = frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) U * Delta_ij x \<omega> \<omega>0 \<omega>s i j"
proof -
  have perpi: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  have zi: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Phi_par_perp_slot_zero[OF detnz perpi])
  have zj: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Phi_par_perp_slot_zero[OF detnz perpi])
  show ?thesis
    unfolding Jac3_def Delta_ij_def det3_def zi zj by simp
qed

text \<open>The rank-3 conclusion: given the paper's own two nondegeneracy hypotheses
  --- \<open>D\<Phi>_par(U) \<noteq> 0\<close> for some tangent direction U (their \<open>U \<in> E_u, D\<Phi>_1(U)\<noteq>0\<close>)
  and \<open>Delta_ij(i,j) \<noteq> 0\<close> (their own hypothesis) --- the Jac3 determinant is
  nonzero, i.e. the restriction of \<open>D(\<Phi>_par,\<Phi>2,G11)\<close> to \<open>(U,slot_i,slot_j)\<close> is
  a bijective linear map on \<open>R^3\<close> (full rank 3).\<close>

corollary Jac3_nonzero_criterion:
  fixes i j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x U :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and dPhi_par_U_nz: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) U \<noteq> 0"
    and delta_nz: "Delta_ij x \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
  shows "Jac3 x \<omega> \<omega>0 \<omega>s U i j \<noteq> 0"
  unfolding Jac3_identity[OF detnz] using dPhi_par_U_nz delta_nz by simp


section \<open>The symmetric H22 branch (prop:vpair22 / cor:vpair22)\<close>

text \<open>The paper's \<open>prop:vpair22\<close>/\<open>cor:vpair22\<close> (the \<open>H12\<noteq>0,H22\<noteq>0\<close> branch) mirrors
  \<open>prop:vpair11\<close>/\<open>cor:vpair11\<close> almost exactly: SAME \<open>\<Phi>2\<close> factor, SAME block-triangular
  argument with \<open>\<Phi>_1\<close> (our \<open>Phi_par\<close>) independent of every v-slot --- only \<open>G_11\<close> is
  replaced by \<open>G_22 := H11 - H12\<^sup>2/H22\<close>.  \<open>Phi_par\<close>/\<open>Phi_par_perp_slot_zero\<close>/\<open>det3\<close>
  are ALL reused verbatim (they do not depend on the H11/H22 choice at all).\<close>

subsection \<open>G22: the quotient-rule \<open>x\<close>-derivative (fixed \<open>\<omega>\<close>)\<close>

definition G22 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "G22 x \<omega> \<omega>0 \<omega>s = vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
       - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
         / vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2"

theorem has_derivative_G22_x:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  assumes h22nz: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2 \<noteq> 0"
  shows "((\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) has_derivative
      (\<lambda>h. frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) h
         - ((2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h)
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
            - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) h)
           / (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2))) (at x)"
proof -
  have h11: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 1 and l = 1], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h12: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 1 and l = 2], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h22: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 2 and l = 2], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h12sq: "((\<lambda>y. (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2)\<^sup>2) has_derivative
       (\<lambda>h. 2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h))
       (at x)"
    unfolding power2_eq_square
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF h12 h12]]) (simp add: fun_eq_iff algebra_simps)
  have hdiv: "((\<lambda>y. (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2)\<^sup>2
                   / vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2)
       has_derivative
       (\<lambda>h. ((2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h)
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
            - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) h)
           / (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2))) (at x)"
    by (rule has_derivative_divide'[OF h12sq h22 h22nz])
  show ?thesis
    unfolding G22_def
    by (rule has_derivative_diff[OF h11 hdiv])
qed

subsection \<open>G22's perp-slot value\<close>

theorem G22_perp_slot_value:
  fixes m :: "'n::finite" and v \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes h22nz: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2 \<noteq> 0"
    and perp: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> v = 0"
  shows "frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot m v)
       = frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) (slot m v)
       - ((2 * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x)
                  (slot m v))
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
            - (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2)\<^sup>2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x)
                  (slot m v))
           / (vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2
              * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2)"
  by (rule fun_cong[OF frechet_derivative_at[OF has_derivative_G22_x[OF h22nz], symmetric]])

subsection \<open>Delta_ij_22 and its identity\<close>

text \<open>\<open>\<Delta>\<^sub>i\<^sub>j^{(22)} := det \<partial>(\<Phi>2,G22)/\<partial>(v_i,v_j)\<close> --- SAME \<open>\<Phi>2\<close> as \<open>prop:vpair11\<close>,
  now paired with \<open>G22\<close> instead of \<open>G11\<close>.\<close>

definition Delta_ij_22 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Delta_ij_22 x \<omega> \<omega>0 \<omega>s i j =
     frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
         (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       * frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
   - frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
         (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       * frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"

theorem Delta_ij_22_identity:
  fixes i j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes h22nz: "vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2 \<noteq> 0"
  shows "Delta_ij_22 x \<omega> \<omega>0 \<omega>s i j
       = (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
            * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x i))
           * frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
       - (2 * gain_dip \<omega> * (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis 2 1) \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))
            * Im (cnj (vec_nth (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) 1) * phase (cvec_dip \<omega>0 \<omega>s \<omega>) x j))
           * frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))"
proof -
  have perpi: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  show ?thesis
    unfolding Delta_ij_22_def
    by (simp add: Phi2_perp_slot_value[OF perpi])
qed

subsection \<open>Jac3_22 and the rank-3 criterion (cor:vpair22)\<close>

definition Jac3_22 :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2
      \<Rightarrow> (real^2)^'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Jac3_22 x \<omega> \<omega>0 \<omega>s U i j =
     det3
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) U)
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x) U)
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) U)
       (frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. G22 y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))"

theorem Jac3_22_identity:
  fixes i j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x U :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
  shows "Jac3_22 x \<omega> \<omega>0 \<omega>s U i j
       = frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) U * Delta_ij_22 x \<omega> \<omega>0 \<omega>s i j"
proof -
  have perpi: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  have zi: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Phi_par_perp_slot_zero[OF detnz perpi])
  have zj: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Phi_par_perp_slot_zero[OF detnz perpi])
  show ?thesis
    unfolding Jac3_22_def Delta_ij_22_def det3_def zi zj by simp
qed

corollary Jac3_22_nonzero_criterion:
  fixes i j :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x U :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and dPhi_par_U_nz: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) U \<noteq> 0"
    and delta_nz: "Delta_ij_22 x \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
  shows "Jac3_22 x \<omega> \<omega>0 \<omega>s U i j \<noteq> 0"
  unfolding Jac3_22_identity[OF detnz] using dPhi_par_U_nz delta_nz by simp


section \<open>The H12=0,H22\<noteq>0 branch (prop:H12zero/cor:H12zero) --- with an explicit hypothesis\<close>

text \<open>The paper's determinant identity (prop:H12zero) needs \<open>H\<^sub>1\<^sub>1\<close> independent of every
  v-slot, mirroring \<open>\<Phi>\<^sub>1\<close>'s v-independence claim from \<open>cor:vpair11\<close> --- which does NOT
  hold automatically in our angular omega coordinates (that is exactly what \<open>Phi_par\<close>/
  \<open>e_par\<close> fixed, at the FIRST-derivative level).  The natural analogous fix at the
  SECOND-derivative (Hessian) level is \<open>H_par\<close>: contract BOTH Hessian indices with
  \<open>e_par\<close> instead of \<open>axis 1 1\<close>.  Tracing @{thm HessU_dip_entry_perp_slot_value}
  through this contraction, MOST terms collapse the same clean way \<open>Phi_par\<close>'s did ---
  but a residual term from \<open>D2cvec_dip(e_par)(e_par)\<close> does NOT obviously vanish (see
  the diary entry "cor:H12zero investigation" for the differential-geometry argument why
  this is a genuine obstacle, not just an unsimplified artifact --- NOT yet formally
  settled either way).  Rather than assume it away silently, this file carries it as an
  EXPLICIT NAMED HYPOTHESIS on the final rank-3 criterion, so what IS proven is honest:
  every OTHER piece (the block-triangular determinant identity itself, reusing
  \<open>Phi_par_perp_slot_zero\<close> and \<open>Phi2_perp_slot_value\<close> exactly as before) is fully
  verified; only \<open>H_par\<close>'s v-slot vanishing is a carried assumption.\<close>

subsection \<open>H_par: the e_par-contracted Hessian entry\<close>

definition H_par :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real" where
  "H_par x \<omega> \<omega>0 \<omega>s =
     vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
        * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 1
   + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
        * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 1) 2
   + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
        * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 1
   + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
        * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip x \<omega>) 2) 2"

theorem has_derivative_H_par_x:
  fixes \<omega> \<omega>0 \<omega>s :: "real^2"
  shows "((\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) has_derivative
      (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) h
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 1) (at x) h
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) h))
       (at x)"
proof -
  have h11: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 1 and l = 1], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h12: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 1 and l = 2], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h21: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 1) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 1) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 2 and l = 1], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have h22: "((\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) has_derivative
       frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x)) (at x)"
    unfolding frechet_derivative_at[OF has_derivative_HessU_dip_entry_x[where k = 2 and l = 2], symmetric]
    by (rule has_derivative_HessU_dip_entry_x)
  have t1: "((\<lambda>y. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) h))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const h11]]) (simp add: fun_eq_iff algebra_simps)
  have t2: "((\<lambda>y. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
                * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) h))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const h12]]) (simp add: fun_eq_iff algebra_simps)
  have t3: "((\<lambda>y. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
                * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 1) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 1) (at x) h))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const h21]]) (simp add: fun_eq_iff algebra_simps)
  have t4: "((\<lambda>y. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
                * vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
              * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) h))
       (at x)"
    by (rule has_derivative_eq_rhs[OF has_derivative_mult[OF has_derivative_const h22]]) (simp add: fun_eq_iff algebra_simps)
  show ?thesis
    unfolding H_par_def
    by (rule has_derivative_add[OF has_derivative_add[OF has_derivative_add[OF t1 t2] t3] t4])
qed

theorem H_par_slot_value:
  fixes m :: "'n::finite" and v \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  shows "frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m v)
       = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 1) (at x) (slot m v)
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 1) 2) (at x) (slot m v)
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 1) (at x) (slot m v)
        + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2 * vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
             * frechet_derivative (\<lambda>y. vec_nth (vec_nth (HessU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) 2) (at x) (slot m v)"
  by (rule fun_cong[OF frechet_derivative_at[OF has_derivative_H_par_x, symmetric]])

subsection \<open>Packaged u-slot (parallel) values of Phi_par and Phi2\<close>

text \<open>The u-slot direction for triple element \<open>j\<close> is \<open>slot j (cvec_dip \<omega>0 \<omega>s \<omega>)\<close>
  (moving element \<open>j\<close> PARALLEL to \<open>c\<close>, unnormalized --- the same convention as
  \<open>perp2 c\<close> for the v-slot).  These values are kept PACKAGED (raw \<open>dEjm\<close>/\<open>frechet_derivative\<close>
  form), matching the established discipline: only \<open>Phi2_perp_slot_value\<close>'s v-slot form and
  \<open>Phi_par_perp_slot_zero\<close>'s zero are needed in clean closed form for the determinant
  identity below; the u-slot entries can stay packaged.\<close>

theorem Phi_par_uslot_value:
  fixes m :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  shows "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>))
       = vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
           * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)))) 1
       + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
           * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)))) 2"
proof -
  have hd: "((\<lambda>y. e_par \<omega>0 \<omega>s \<omega> \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) has_derivative
       (\<lambda>h. vec_nth (e_par \<omega>0 \<omega>s \<omega>) 1
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 1
            + vec_nth (e_par \<omega>0 \<omega>s \<omega>) 2
              * vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                   (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                   (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                   (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
    by (rule has_derivative_gradU_inner_x)
  have eq: "(\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) = (\<lambda>y. e_par \<omega>0 \<omega>s \<omega> \<bullet> gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>)"
    by (rule ext) (simp add: Phi_par_def inner_commute)
  show ?thesis
    unfolding eq
    by (rule fun_cong[OF frechet_derivative_at[OF hd, symmetric]])
qed

theorem Phi2_uslot_value:
  fixes m :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  shows "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
             (slot m (cvec_dip \<omega>0 \<omega>s \<omega>))
       = vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) (slot m (cvec_dip \<omega>0 \<omega>s \<omega>)))) 2"
proof -
  have hd2: "((\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) has_derivative
       (\<lambda>h. vec_nth (\<chi> j. dEjm (frechet_derivative gdip (at (vec_nth \<omega> 1)) (vec_nth (axis j 1) 1))
                  (gain_dip \<omega>) (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 1)
                  (vec_nth (Dcvec_dip \<omega>0 \<omega>s \<omega> (axis j 1)) 2)
                  (M_paper x (cvec_dip \<omega>0 \<omega>s \<omega>)) (DM_paper_x x (cvec_dip \<omega>0 \<omega>s \<omega>) h)) 2)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth has_derivative_gradU_dip_x_explicit])
  show ?thesis
    by (rule fun_cong[OF frechet_derivative_at[OF hd2, symmetric]])
qed

subsection \<open>Lambda_ij: the u-slot determinant of (Phi_par, H_par)\<close>

definition Lambda_ij :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Lambda_ij x \<omega> \<omega>0 \<omega>s i j =
     frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))
       * frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
   - frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
       * frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))"

subsection \<open>The block-triangular 3x3 Jacobian and the rank-3 criterion\<close>

definition Jac3_H12zero :: "(real^2)^'n::finite \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> real^2 \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> real" where
  "Jac3_H12zero x \<omega> \<omega>0 \<omega>s i j k =
     det3
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
            (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))
       (frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       (frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))))"

text \<open>\<^bold>\<open>The one place a genuinely unverified hypothesis enters\<close>: \<open>H_par\<close>'s value at the
  perpendicular slot for element \<open>k\<close> is assumed zero, NOT proven --- see the section
  intro and the diary entry.  Every other ingredient below is a fully verified reuse of
  existing bridge theorems.\<close>

theorem Jac3_H12zero_identity:
  fixes i j k :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and h_par_vslot_zero: \<comment> \<open>UNVERIFIED (see above): the residual D2cvec_dip term\<close>
      "frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
  shows "Jac3_H12zero x \<omega> \<omega>0 \<omega>s i j k
       = frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))
           * (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
                  (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
                * 0
              - frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
                  (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
                * frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>)))
       - frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot j (cvec_dip \<omega>0 \<omega>s \<omega>))
           * (frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
                  (slot i (cvec_dip \<omega>0 \<omega>s \<omega>))
                * 0
              - frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
                  (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>)))
                * frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot i (cvec_dip \<omega>0 \<omega>s \<omega>)))"
proof -
  have perpi: "cvec_dip \<omega>0 \<omega>s \<omega> \<bullet> perp2 (cvec_dip \<omega>0 \<omega>s \<omega>) = 0"
    by (rule perp2_orth)
  have zk: "frechet_derivative (\<lambda>y. Phi_par y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    by (rule Phi_par_perp_slot_zero[OF detnz perpi])
  show ?thesis
    unfolding Jac3_H12zero_def det3_def zk h_par_vslot_zero by simp
qed

corollary Jac3_H12zero_nonzero_criterion:
  fixes i j k :: "'n::finite" and \<omega> \<omega>0 \<omega>s :: "real^2" and x :: "(real^2)^'n"
  assumes detnz: "det (matrix (Dcvec_dip \<omega>0 \<omega>s \<omega>)) \<noteq> 0"
    and h_par_vslot_zero:
      "frechet_derivative (\<lambda>y. H_par y \<omega> \<omega>0 \<omega>s) (at x) (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) = 0"
    and s_k_nz:
      "frechet_derivative (\<lambda>y. vec_nth (gradU (cvec_dip \<omega>0 \<omega>s) gain_dip y \<omega>) 2) (at x)
           (slot k (perp2 (cvec_dip \<omega>0 \<omega>s \<omega>))) \<noteq> 0"
    and lambda_nz: "Lambda_ij x \<omega> \<omega>0 \<omega>s i j \<noteq> 0"
  shows "Jac3_H12zero x \<omega> \<omega>0 \<omega>s i j k \<noteq> 0"
  unfolding Jac3_H12zero_identity[OF detnz h_par_vslot_zero] Lambda_ij_def[symmetric]
  using s_k_nz lambda_nz unfolding Lambda_ij_def by (simp add: algebra_simps)

end
