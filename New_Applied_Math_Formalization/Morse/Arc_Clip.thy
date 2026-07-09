theory Arc_Clip
  imports "HOL-Analysis.Analysis"
begin

text \<open>IVT phrased for @{term continuous_on}: a value between two attained values is attained.\<close>
lemma ivt_conn:
  fixes g :: "real \<Rightarrow> real"
  assumes cont: "continuous_on {lo..hi} g"
      and p: "p \<in> {lo..hi}" and q: "q \<in> {lo..hi}"
      and le1: "g p \<le> y" and le2: "y \<le> g q"
  shows "\<exists>u\<in>{lo..hi}. g u = y"
proof -
  have conn: "connected (g ` {lo..hi})"
    using connected_continuous_image[OF cont connected_Icc] .
  have gp: "g p \<in> g ` {lo..hi}" using p by blast
  have gq: "g q \<in> g ` {lo..hi}" using q by blast
  have "{g p .. g q} \<subseteq> g ` {lo..hi}"
    using connected_contains_Icc[OF conn gp gq] .
  moreover have "y \<in> {g p .. g q}" using le1 le2 by simp
  ultimately have "y \<in> g ` {lo..hi}" by blast
  thus ?thesis by blast
qed

text \<open>If the open cell avoids the level @{term c} and the closed cell is not entirely
  @{text "\<le> c"}, then any sublevel point of the cell must be an exact level point.
  Key fact: a strict sublevel point and a strict superlevel point bracket an
  IVT crossing that is forced to lie strictly inside the cell.\<close>
lemma cell_complete:
  fixes g :: "real \<Rightarrow> real"
  assumes cont: "continuous_on {lo..hi} g"
      and open_avoid: "\<And>t. \<lbrakk>lo < t; t < hi\<rbrakk> \<Longrightarrow> g t \<noteq> c"
      and s: "s \<in> {lo..hi}" and gs: "g s \<le> c"
      and notall: "\<not> (\<forall>t\<in>{lo..hi}. g t \<le> c)"
  shows "g s = c"
proof (rule ccontr)
  assume "g s \<noteq> c"
  with gs have gs_lt: "g s < c" by simp
  from notall obtain t0 where t0: "t0 \<in> {lo..hi}" and gt0: "g t0 > c" by force
  have los: "lo \<le> s" and shi: "s \<le> hi" using s by auto
  have lot0: "lo \<le> t0" and t0hi: "t0 \<le> hi" using t0 by auto
  \<comment> \<open>IVT between @{term s} and @{term t0} gives an interior crossing @{term u}.\<close>
  consider (le) "s \<le> t0" | (ge) "t0 \<le> s" by linarith
  then show False
  proof cases
    case le
    have sub: "{s..t0} \<subseteq> {lo..hi}" using los t0hi by auto
    have "\<exists>u\<in>{s..t0}. g u = c"
    proof (rule ivt_conn[OF continuous_on_subset[OF cont sub]])
      show "s \<in> {s..t0}" using le by simp
      show "t0 \<in> {s..t0}" using le by simp
      show "g s \<le> c" using gs_lt by simp
      show "c \<le> g t0" using gt0 by simp
    qed
    then obtain u where u: "u \<in> {s..t0}" and gu: "g u = c" by blast
    \<comment> \<open>g s < c with g u = c gives s < u; g u = c with c < g t0 gives u < t0.\<close>
    have "s \<noteq> u" using gu gs_lt by force
    with u have "s < u" by simp
    moreover have "u \<noteq> t0" using gu gt0 by force
    with u have "u < t0" by simp
    ultimately have "lo < u" "u < hi" using los t0hi by auto
    from open_avoid[OF this] gu show False by simp
  next
    case ge
    have sub: "{t0..s} \<subseteq> {lo..hi}" using lot0 shi by auto
    have "\<exists>u\<in>{t0..s}. g u = c"
    proof (rule ivt_conn[OF continuous_on_subset[OF cont sub]])
      show "s \<in> {t0..s}" using ge by simp
      show "t0 \<in> {t0..s}" using ge by simp
      show "g s \<le> c" using gs_lt by simp
      show "c \<le> g t0" using gt0 by simp
    qed
    then obtain u where u: "u \<in> {t0..s}" and gu: "g u = c" by blast
    have "u \<noteq> s" using gu gs_lt by force
    with u have "u < s" by simp
    moreover have "t0 \<noteq> u" using gu gt0 by force
    with u have "t0 < u" by simp
    ultimately have "lo < u" "u < hi" using lot0 shi by auto
    from open_avoid[OF this] gu show False by simp
  qed
qed

text \<open>DELIVERABLE 1: a continuous function on a closed interval whose level set is finite
  has sublevel set equal to a finite union of closed subintervals.\<close>
lemma finite_sublevel_as_interval_union:
  fixes g :: "real \<Rightarrow> real" and a b c :: real
  assumes cont: "continuous_on {a..b} g"
      and fin: "finite {s \<in> {a..b}. g s = c}"
  shows "\<exists>P::(real\<times>real) set. finite P \<and>
           {s \<in> {a..b}. g s \<le> c} = (\<Union>(lo,hi)\<in>P. {lo..hi}) \<and>
           (\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b)"
proof (cases "a \<le> b")
  case False
  \<comment> \<open>Empty interval: take @{term "P = {}"}.\<close>
  have "{s \<in> {a..b}. g s \<le> c} = (\<Union>(lo,hi)\<in>{}. {lo..hi})"
    using False by simp
  thus ?thesis by (intro exI[of _ "{}"]) simp
next
  case True
  define Z where "Z = {s \<in> {a..b}. g s = c}"
  define F where "F = insert a (insert b Z)"
  have finZ: "finite Z" using fin Z_def by simp
  have finF: "finite F" using finZ F_def by simp
  have F_in: "\<And>x. x \<in> F \<Longrightarrow> a \<le> x \<and> x \<le> b"
    using True Z_def F_def by auto
  have F_ab: "F \<subseteq> {a..b}" using F_in by auto
  have aF: "a \<in> F" and bF: "b \<in> F" using F_def by auto
  \<comment> \<open>Genuine cells: consecutive elements of @{term F} on which @{term g} stays @{text "\<le> c"}.\<close>
  define P1 where "P1 = {(lo,hi). lo \<in> F \<and> hi \<in> F \<and> lo \<le> hi \<and>
                     (\<forall>x\<in>F. \<not>(lo < x \<and> x < hi)) \<and> (\<forall>t\<in>{lo..hi}. g t \<le> c)}"
  define P where "P = P1 \<union> ((\<lambda>s. (s,s)) ` Z)"
  have P1sub: "P1 \<subseteq> F \<times> F" unfolding P1_def by auto
  have finP1: "finite P1" using P1sub finF by (simp add: finite_subset)
  have finP: "finite P" unfolding P_def using finP1 finZ by simp
  \<comment> \<open>Bounds.\<close>
  have bounds: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b"
  proof (clarify)
    fix lo hi assume "(lo,hi) \<in> P"
    then consider (p1) "(lo,hi) \<in> P1" | (z) "(lo,hi) \<in> (\<lambda>s. (s,s)) ` Z"
      unfolding P_def by blast
    thus "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b"
    proof cases
      case p1
      then have "lo \<in> F" "hi \<in> F" "lo \<le> hi" unfolding P1_def by auto
      thus ?thesis using F_in by auto
    next
      case z
      then obtain s where "s \<in> Z" "lo = s" "hi = s" by auto
      thus ?thesis using Z_def True by auto
    qed
  qed
  \<comment> \<open>Soundness: every covered point is a sublevel point of @{term "{a..b}"}.\<close>
  have sound: "(\<Union>(lo,hi)\<in>P. {lo..hi}) \<subseteq> {s \<in> {a..b}. g s \<le> c}"
  proof (clarify)
    fix t lo hi assume mem: "(lo,hi) \<in> P" and t: "t \<in> {lo..hi}"
    from mem bounds have bd: "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b" by blast
    with t have tab: "t \<in> {a..b}" by auto
    from mem consider (p1) "(lo,hi) \<in> P1" | (z) "(lo,hi) \<in> (\<lambda>s. (s,s)) ` Z"
      unfolding P_def by blast
    then have "g t \<le> c"
    proof cases
      case p1
      then have "\<forall>t\<in>{lo..hi}. g t \<le> c" unfolding P1_def by auto
      thus ?thesis using t by blast
    next
      case z
      then obtain s where "s \<in> Z" "lo = s" "hi = s" by auto
      then have "t = s" using t by simp
      thus ?thesis using \<open>s \<in> Z\<close> Z_def by auto
    qed
    with tab show "t \<in> {a..b} \<and> g t \<le> c" by simp
  qed
  \<comment> \<open>Completeness: every sublevel point lies in some cell of @{term P}.\<close>
  have complete: "{s \<in> {a..b}. g s \<le> c} \<subseteq> (\<Union>(lo,hi)\<in>P. {lo..hi})"
  proof (clarify)
    fix s assume sab: "s \<in> {a..b}" and gs: "g s \<le> c"
    have sab': "a \<le> s" "s \<le> b" using sab by auto
    \<comment> \<open>Floor and ceiling of @{term s} within @{term F}.\<close>
    define lo where "lo = Max {x \<in> F. x \<le> s}"
    define hi where "hi = Min {x \<in> F. s \<le> x}"
    have neL: "{x \<in> F. x \<le> s} \<noteq> {}" using aF sab' by auto
    have neR: "{x \<in> F. s \<le> x} \<noteq> {}" using bF sab' by auto
    have finL: "finite {x \<in> F. x \<le> s}" using finF by simp
    have finR: "finite {x \<in> F. s \<le> x}" using finF by simp
    have loF: "lo \<in> F" and lo_le: "lo \<le> s"
      using Max_in[OF finL neL] lo_def by auto
    have hiF: "hi \<in> F" and s_le_hi: "s \<le> hi"
      using Min_in[OF finR neR] hi_def by auto
    have lohi: "lo \<le> hi" using lo_le s_le_hi by simp
    have s_mem: "s \<in> {lo..hi}" using lo_le s_le_hi by simp
    \<comment> \<open>No element of @{term F} lies strictly between @{term lo} and @{term hi}.\<close>
    have no_between: "\<forall>x\<in>F. \<not>(lo < x \<and> x < hi)"
    proof (intro ballI notI)
      fix x assume xF: "x \<in> F" and xbtw: "lo < x \<and> x < hi"
      then have xlo: "lo < x" and xhi: "x < hi" by auto
      show False
      proof (cases "x \<le> s")
        case True
        then have "x \<in> {y \<in> F. y \<le> s}" using xF by simp
        then have "x \<le> lo" using Max_ge[OF finL] lo_def by simp
        thus False using xlo by simp
      next
        case False
        then have "s \<le> x" by simp
        then have "x \<in> {y \<in> F. s \<le> y}" using xF by simp
        then have "hi \<le> x" using Min_le[OF finR] hi_def by simp
        thus False using xhi by simp
      qed
    qed
    \<comment> \<open>The cell @{term "{lo..hi}"} lies inside @{term "{a..b}"}.\<close>
    have lo_ab: "a \<le> lo" and hi_ab: "hi \<le> b" using F_in[OF loF] F_in[OF hiF] by auto
    have cell_sub: "{lo..hi} \<subseteq> {a..b}" using lo_ab hi_ab by auto
    have cell_cont: "continuous_on {lo..hi} g"
      using continuous_on_subset[OF cont cell_sub] .
    \<comment> \<open>Open cell avoids the level @{term c}.\<close>
    have open_avoid: "\<And>t. \<lbrakk>lo < t; t < hi\<rbrakk> \<Longrightarrow> g t \<noteq> c"
    proof
      fix t assume "lo < t" "t < hi" and gtc: "g t = c"
      have "a \<le> t" "t \<le> b" using \<open>lo < t\<close> \<open>t < hi\<close> lo_ab hi_ab by auto
      then have "t \<in> Z" using gtc Z_def by simp
      then have "t \<in> F" using F_def by simp
      with no_between \<open>lo < t\<close> \<open>t < hi\<close> show False by blast
    qed
    \<comment> \<open>Dichotomy from @{thm cell_complete}.\<close>
    show "s \<in> (\<Union>(lo,hi)\<in>P. {lo..hi})"
    proof (cases "\<forall>t\<in>{lo..hi}. g t \<le> c")
      case True
      \<comment> \<open>Genuine qualifying cell.\<close>
      have "(lo,hi) \<in> P1"
        unfolding P1_def using loF hiF lohi no_between True by simp
      then have inP: "(lo,hi) \<in> P" unfolding P_def by simp
      show ?thesis using s_mem inP by blast
    next
      case False
      \<comment> \<open>Then @{term s} is an exact level point, covered by a degenerate cell.\<close>
      have notall: "\<not> (\<forall>t\<in>{lo..hi}. g t \<le> c)" using False by simp
      have "g s = c"
        by (rule cell_complete[OF cell_cont open_avoid s_mem gs notall])
      then have "s \<in> Z" using sab Z_def by simp
      then have inP: "(s,s) \<in> P" unfolding P_def by simp
      moreover have "s \<in> {s..s}" by simp
      ultimately show ?thesis by blast
    qed
  qed
  have "{s \<in> {a..b}. g s \<le> c} = (\<Union>(lo,hi)\<in>P. {lo..hi})"
    using sound complete by blast
  thus ?thesis using finP bounds by blast
qed

text \<open>DELIVERABLE 2: clipping a C1 plane arc by a half-plane.  Applying Deliverable 1 to the
  @{term i}-th coordinate gives a finite interval-union decomposition of the parameters where the
  coordinate stays @{text "\<le> c"}; on each closed subinterval the arc is still C1.\<close>
lemma C1_arc_clip_halfplane:
  fixes \<gamma> :: "real \<Rightarrow> real^2" and a b c :: real and i :: "2"
  assumes c1: "\<gamma> C1_differentiable_on {a..b}"
      and fin: "finite {s \<in> {a..b}. (\<gamma> s)$i = c}"
  shows "\<exists>P::(real\<times>real) set. finite P \<and>
           {s \<in> {a..b}. (\<gamma> s)$i \<le> c} = (\<Union>(lo,hi)\<in>P. {lo..hi}) \<and>
           (\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi})"
proof -
  \<comment> \<open>The coordinate map is continuous, being the @{term i}-th component of a C1 (hence continuous) arc.\<close>
  have cg: "continuous_on {a..b} \<gamma>"
    using C1_differentiable_imp_continuous_on[OF c1] .
  have cont: "continuous_on {a..b} (\<lambda>s. (\<gamma> s)$i)"
  proof -
    have "continuous_on {a..b} ((\<lambda>x. x$i) \<circ> \<gamma>)"
      by (rule continuous_on_compose[OF cg linear_continuous_on[OF bounded_linear_vec_nth]])
    thus ?thesis by (simp add: o_def)
  qed
  \<comment> \<open>Apply Deliverable 1 to @{term "\<lambda>s. (\<gamma> s)$i"}.\<close>
  obtain P :: "(real\<times>real) set" where
    finP: "finite P" and
    eqP: "{s \<in> {a..b}. (\<gamma> s)$i \<le> c} = (\<Union>(lo,hi)\<in>P. {lo..hi})" and
    boundsP: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b"
    using finite_sublevel_as_interval_union[OF cont fin] by blast
  \<comment> \<open>On each subinterval the arc stays C1 by restriction.\<close>
  have c1P: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
  proof (clarify)
    fix lo hi assume "(lo,hi) \<in> P"
    with boundsP have bd: "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b" by blast
    then have "{lo..hi} \<subseteq> {a..b}" by auto
    then have "\<gamma> C1_differentiable_on {lo..hi}"
      using C1_differentiable_on_subset[OF c1] by blast
    with bd show "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}" by simp
  qed
  show ?thesis using finP eqP c1P by blast
qed

text \<open>DELIVERABLE 1: superlevel companion of @{thm C1_arc_clip_halfplane}.\<close>
lemma C1_arc_clip_halfplane_ge:
  fixes \<gamma> :: "real \<Rightarrow> real^2" and a b c :: real and i :: "2"
  assumes c1: "\<gamma> C1_differentiable_on {a..b}"
      and fin: "finite {s \<in> {a..b}. (\<gamma> s)$i = c}"
  shows "\<exists>P::(real\<times>real) set. finite P \<and>
           {s \<in> {a..b}. (\<gamma> s)$i \<ge> c} = (\<Union>(lo,hi)\<in>P. {lo..hi}) \<and>
           (\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi})"
proof -
  have cg: "continuous_on {a..b} \<gamma>"
    using C1_differentiable_imp_continuous_on[OF c1] .
  have cont_i: "continuous_on {a..b} (\<lambda>s. (\<gamma> s)$i)"
  proof -
    have "continuous_on {a..b} ((\<lambda>x. x$i) \<circ> \<gamma>)"
      by (rule continuous_on_compose[OF cg linear_continuous_on[OF bounded_linear_vec_nth]])
    thus ?thesis by (simp add: o_def)
  qed
  have cont: "continuous_on {a..b} (\<lambda>s. - ((\<gamma> s)$i))"
    using continuous_on_minus[OF cont_i] .
  have fin': "finite {s \<in> {a..b}. - ((\<gamma> s)$i) = - c}"
  proof -
    have "{s \<in> {a..b}. - ((\<gamma> s)$i) = - c} = {s \<in> {a..b}. (\<gamma> s)$i = c}" by auto
    thus ?thesis using fin by simp
  qed
  obtain P :: "(real\<times>real) set" where
    finP: "finite P" and
    eqP: "{s \<in> {a..b}. - ((\<gamma> s)$i) \<le> - c} = (\<Union>(lo,hi)\<in>P. {lo..hi})" and
    boundsP: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b"
    using finite_sublevel_as_interval_union[OF cont fin'] by blast
  have eqset: "{s \<in> {a..b}. (\<gamma> s)$i \<ge> c} = {s \<in> {a..b}. - ((\<gamma> s)$i) \<le> - c}" by auto
  have eqP': "{s \<in> {a..b}. (\<gamma> s)$i \<ge> c} = (\<Union>(lo,hi)\<in>P. {lo..hi})"
    using eqset eqP by simp
  have c1P: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
  proof (clarify)
    fix lo hi assume "(lo,hi) \<in> P"
    with boundsP have bd: "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b" by blast
    then have "{lo..hi} \<subseteq> {a..b}" by auto
    then have "\<gamma> C1_differentiable_on {lo..hi}"
      using C1_differentiable_on_subset[OF c1] by blast
    with bd show "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}" by simp
  qed
  show ?thesis using finP eqP' c1P by blast
qed

text \<open>HELPER: intersection of two finite interval-unions (cells in @{term "{a..b}"}, nondegenerate,
  carrying C1) is again a finite interval-union with the same properties.\<close>
lemma inter_interval_union:
  fixes a b :: real and \<gamma> :: "real \<Rightarrow> real^2"
  assumes finP: "finite P" and finQ: "finite Q"
      and bP: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
      and bQ: "\<forall>(lo,hi)\<in>Q. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
  shows "\<exists>R::(real\<times>real) set. finite R \<and>
           (\<Union>(lo,hi)\<in>P. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>Q. {lo..hi}) = (\<Union>(lo,hi)\<in>R. {lo..hi}) \<and>
           (\<forall>(lo,hi)\<in>R. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi})"
proof -
  define R0 where "R0 = (\<lambda>((lo,hi),(lo',hi')). (max lo lo', min hi hi')) ` (P \<times> Q)"
  define R where "R = {(lo,hi)\<in>R0. lo \<le> hi}"
  have finR0: "finite R0" unfolding R0_def using finP finQ by simp
  have Rsub: "R \<subseteq> R0" unfolding R_def by auto
  have finR: "finite R" using finR0 Rsub by (rule finite_subset[rotated])
  have raw: "(\<Union>(lo,hi)\<in>P. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>Q. {lo..hi}) = (\<Union>(lo,hi)\<in>R0. {lo..hi})"
  proof
    show "(\<Union>(lo,hi)\<in>P. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>Q. {lo..hi}) \<subseteq> (\<Union>(lo,hi)\<in>R0. {lo..hi})"
    proof (clarify)
      fix t lo hi lo' hi'
      assume "(lo,hi) \<in> P" "t \<in> {lo..hi}" "(lo',hi') \<in> Q" "t \<in> {lo'..hi'}"
      then have "t \<in> {max lo lo' .. min hi hi'}" by simp
      moreover have "(max lo lo', min hi hi') \<in> R0"
        unfolding R0_def using \<open>(lo,hi)\<in>P\<close> \<open>(lo',hi')\<in>Q\<close> by force
      ultimately show "t \<in> (\<Union>(lo,hi)\<in>R0. {lo..hi})" by blast
    qed
  next
    show "(\<Union>(lo,hi)\<in>R0. {lo..hi}) \<subseteq> (\<Union>(lo,hi)\<in>P. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>Q. {lo..hi})"
    proof (clarify)
      fix t lo hi assume "(lo,hi) \<in> R0" "t \<in> {lo..hi}"
      then obtain p q where pq: "p \<in> P" "q \<in> Q" and
        eq: "(lo,hi) = (case (p,q) of ((lo,hi),(lo',hi')) \<Rightarrow> (max lo lo', min hi hi'))"
        unfolding R0_def by auto
      obtain pl ph where p: "p = (pl,ph)" by (cases p)
      obtain ql qh where q: "q = (ql,qh)" by (cases q)
      from eq p q have loeq: "lo = max pl ql" and hieq: "hi = min ph qh" by auto
      from \<open>t \<in> {lo..hi}\<close> loeq hieq have "t \<in> {pl..ph}" "t \<in> {ql..qh}" by auto
      moreover have "(pl,ph) \<in> P" using pq p by simp
      moreover have "(ql,qh) \<in> Q" using pq q by simp
      ultimately show "t \<in> (\<Union>(lo,hi)\<in>P. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>Q. {lo..hi})" by blast
    qed
  qed
  have drop: "(\<Union>(lo,hi)\<in>R0. {lo..hi}) = (\<Union>(lo,hi)\<in>R. {lo..hi})"
  proof
    show "(\<Union>(lo,hi)\<in>R0. {lo..hi}) \<subseteq> (\<Union>(lo,hi)\<in>R. {lo..hi})"
    proof (clarify)
      fix t lo hi assume "(lo,hi) \<in> R0" "t \<in> {lo..hi}"
      then have "lo \<le> hi" by simp
      with \<open>(lo,hi) \<in> R0\<close> have "(lo,hi) \<in> R" unfolding R_def by simp
      thus "t \<in> (\<Union>(lo,hi)\<in>R. {lo..hi})" using \<open>t \<in> {lo..hi}\<close> by blast
    qed
  next
    show "(\<Union>(lo,hi)\<in>R. {lo..hi}) \<subseteq> (\<Union>(lo,hi)\<in>R0. {lo..hi})"
      unfolding R_def by blast
  qed
  have eqR: "(\<Union>(lo,hi)\<in>P. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>Q. {lo..hi}) = (\<Union>(lo,hi)\<in>R. {lo..hi})"
    using raw drop by simp
  have boundsR: "\<forall>(lo,hi)\<in>R. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
  proof (clarify)
    fix lo hi assume "(lo,hi) \<in> R"
    then have inR0: "(lo,hi) \<in> R0" and lohi: "lo \<le> hi" unfolding R_def by auto
    from inR0 obtain p q where pq: "p \<in> P" "q \<in> Q" and
      eq: "(lo,hi) = (case (p,q) of ((lo,hi),(lo',hi')) \<Rightarrow> (max lo lo', min hi hi'))"
      unfolding R0_def by auto
    obtain pl ph where p: "p = (pl,ph)" by (cases p)
    obtain ql qh where q: "q = (ql,qh)" by (cases q)
    from eq p q have loeq: "lo = max pl ql" and hieq: "hi = min ph qh" by auto
    have Pp: "a \<le> pl \<and> pl \<le> ph \<and> ph \<le> b \<and> \<gamma> C1_differentiable_on {pl..ph}"
      using bP pq p by blast
    have Qq: "a \<le> ql \<and> ql \<le> qh \<and> qh \<le> b \<and> \<gamma> C1_differentiable_on {ql..qh}"
      using bQ pq q by blast
    have alo: "a \<le> lo" using loeq Pp Qq by (simp add: le_max_iff_disj)
    have hib: "hi \<le> b" using hieq Pp Qq by (simp add: min_le_iff_disj)
    have "{lo..hi} \<subseteq> {pl..ph}" using loeq hieq by simp
    then have c1cell: "\<gamma> C1_differentiable_on {lo..hi}"
      using C1_differentiable_on_subset Pp by blast
    show "a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
      using alo lohi hib c1cell by simp
  qed
  show ?thesis using finR eqR boundsR by blast
qed

text \<open>DELIVERABLE 2: clipping a C1 plane arc by a closed box @{term "cbox u v"}.\<close>
lemma arc_inter_cbox_finite_subarcs:
  fixes \<gamma> :: "real \<Rightarrow> real^2" and a b :: real and u v :: "real^2"
  assumes c1: "\<gamma> C1_differentiable_on {a..b}"
      and f1l: "finite {s \<in> {a..b}. (\<gamma> s)$1 = u$1}" and f1h: "finite {s \<in> {a..b}. (\<gamma> s)$1 = v$1}"
      and f2l: "finite {s \<in> {a..b}. (\<gamma> s)$2 = u$2}" and f2h: "finite {s \<in> {a..b}. (\<gamma> s)$2 = v$2}"
  shows "\<exists>P::(real\<times>real) set. finite P \<and>
           {s \<in> {a..b}. \<gamma> s \<in> cbox u v} = (\<Union>(lo,hi)\<in>P. {lo..hi}) \<and>
           (\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi})"
proof -
  \<comment> \<open>The box membership decomposes into the four coordinate half-plane conditions.\<close>
  have memdec: "\<And>s. (\<gamma> s \<in> cbox u v) \<longleftrightarrow>
      ((\<gamma> s)$1 \<ge> u$1 \<and> (\<gamma> s)$1 \<le> v$1 \<and> (\<gamma> s)$2 \<ge> u$2 \<and> (\<gamma> s)$2 \<le> v$2)"
  proof -
    fix s
    have "(\<gamma> s \<in> cbox u v) \<longleftrightarrow> (\<forall>i. u$i \<le> (\<gamma> s)$i \<and> (\<gamma> s)$i \<le> v$i)"
      by (rule mem_box_cart)
    also have "\<dots> \<longleftrightarrow> ((\<gamma> s)$1 \<ge> u$1 \<and> (\<gamma> s)$1 \<le> v$1 \<and> (\<gamma> s)$2 \<ge> u$2 \<and> (\<gamma> s)$2 \<le> v$2)"
      by (metis (full_types) exhaust_2)
    finally show "(\<gamma> s \<in> cbox u v) \<longleftrightarrow>
        ((\<gamma> s)$1 \<ge> u$1 \<and> (\<gamma> s)$1 \<le> v$1 \<and> (\<gamma> s)$2 \<ge> u$2 \<and> (\<gamma> s)$2 \<le> v$2)" .
  qed
  \<comment> \<open>The clipped parameter set is the intersection of the four half-plane factors.\<close>
  have setdec: "{s \<in> {a..b}. \<gamma> s \<in> cbox u v} =
      {s \<in> {a..b}. (\<gamma> s)$1 \<ge> u$1} \<inter> {s \<in> {a..b}. (\<gamma> s)$1 \<le> v$1} \<inter>
      {s \<in> {a..b}. (\<gamma> s)$2 \<ge> u$2} \<inter> {s \<in> {a..b}. (\<gamma> s)$2 \<le> v$2}"
    using memdec by blast
  \<comment> \<open>Each factor is a finite interval-union carrying C1.\<close>
  obtain A where finA: "finite A" and
    eqA: "{s \<in> {a..b}. (\<gamma> s)$1 \<ge> u$1} = (\<Union>(lo,hi)\<in>A. {lo..hi})" and
    bA: "\<forall>(lo,hi)\<in>A. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using C1_arc_clip_halfplane_ge[OF c1 f1l] by blast
  obtain B where finB: "finite B" and
    eqB: "{s \<in> {a..b}. (\<gamma> s)$1 \<le> v$1} = (\<Union>(lo,hi)\<in>B. {lo..hi})" and
    bB: "\<forall>(lo,hi)\<in>B. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using C1_arc_clip_halfplane[OF c1 f1h] by blast
  obtain C where finC: "finite C" and
    eqC: "{s \<in> {a..b}. (\<gamma> s)$2 \<ge> u$2} = (\<Union>(lo,hi)\<in>C. {lo..hi})" and
    bC: "\<forall>(lo,hi)\<in>C. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using C1_arc_clip_halfplane_ge[OF c1 f2l] by blast
  obtain D where finD: "finite D" and
    eqD: "{s \<in> {a..b}. (\<gamma> s)$2 \<le> v$2} = (\<Union>(lo,hi)\<in>D. {lo..hi})" and
    bD: "\<forall>(lo,hi)\<in>D. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using C1_arc_clip_halfplane[OF c1 f2h] by blast
  \<comment> \<open>Fold the four factors through the pairwise intersection helper.\<close>
  obtain AB where finAB: "finite AB" and
    eqAB: "(\<Union>(lo,hi)\<in>A. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>B. {lo..hi}) = (\<Union>(lo,hi)\<in>AB. {lo..hi})" and
    bAB: "\<forall>(lo,hi)\<in>AB. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using inter_interval_union[OF finA finB bA bB] by blast
  obtain ABC where finABC: "finite ABC" and
    eqABC: "(\<Union>(lo,hi)\<in>AB. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>C. {lo..hi}) = (\<Union>(lo,hi)\<in>ABC. {lo..hi})" and
    bABC: "\<forall>(lo,hi)\<in>ABC. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using inter_interval_union[OF finAB finC bAB bC] by blast
  obtain P where finP: "finite P" and
    eqP0: "(\<Union>(lo,hi)\<in>ABC. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>D. {lo..hi}) = (\<Union>(lo,hi)\<in>P. {lo..hi})" and
    bP: "\<forall>(lo,hi)\<in>P. a \<le> lo \<and> lo \<le> hi \<and> hi \<le> b \<and> \<gamma> C1_differentiable_on {lo..hi}"
    using inter_interval_union[OF finABC finD bABC bD] by blast
  \<comment> \<open>Assemble: the clipped set equals the final interval-union.\<close>
  have "{s \<in> {a..b}. \<gamma> s \<in> cbox u v} =
        ((\<Union>(lo,hi)\<in>A. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>B. {lo..hi})) \<inter>
        (\<Union>(lo,hi)\<in>C. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>D. {lo..hi})"
    using setdec eqA eqB eqC eqD by (simp add: Int_assoc)
  also have "\<dots> = (\<Union>(lo,hi)\<in>AB. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>C. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>D. {lo..hi})"
    using eqAB by simp
  also have "\<dots> = (\<Union>(lo,hi)\<in>ABC. {lo..hi}) \<inter> (\<Union>(lo,hi)\<in>D. {lo..hi})"
    using eqABC by (simp add: Int_assoc)
  also have "\<dots> = (\<Union>(lo,hi)\<in>P. {lo..hi})"
    using eqP0 by simp
  finally have eqfin: "{s \<in> {a..b}. \<gamma> s \<in> cbox u v} = (\<Union>(lo,hi)\<in>P. {lo..hi})" .
  show ?thesis using finP eqfin bP by blast
qed

end
