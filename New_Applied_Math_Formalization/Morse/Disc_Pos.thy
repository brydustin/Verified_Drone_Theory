theory Disc_Pos
  imports Complex_Main
begin

lemma detH_indef_abstract:
  fixes Ac Bc P Q R k2 s2 kk ss :: real
  assumes pyth2: "k2*k2 + s2*s2 = 1"
      and pyth1: "kk*kk + ss*ss = 1"
      and th0: "(Bc - P*kk)*k2 + (-Ac + Q*kk)*s2 + R*ss = 0"
      and d2:  "-(Bc - P*kk)*s2 + (-Ac + Q*kk)*k2 = 0"
      and d1:  "(P*ss)*k2 + (-Q*ss)*s2 + R*kk = 0"
  shows "((P*kk)*k2 + (-Q*kk)*s2 + (-R*ss)) * (-(Bc - P*kk)*k2 - (-Ac + Q*kk)*s2)
         - (-(P*ss)*s2 + (-Q*ss)*k2)^2
       = -(P^2 + Q^2 + R^2) * (ss^2)"
  using assms by algebra

lemma gamma_pos:
  fixes Ac Bc P Q R k2 s2 kk ss :: real
  assumes pyth2: "k2*k2 + s2*s2 = 1"
      and th0: "(Bc - P*kk)*k2 + (-Ac + Q*kk)*s2 + R*ss = 0"
      and d2:  "-(Bc - P*kk)*s2 + (-Ac + Q*kk)*k2 = 0"
      and ss_ne: "ss \<noteq> 0"
      and kdiff: "Ac \<noteq> 0 \<or> Bc \<noteq> 0"
  shows "P^2 + Q^2 + R^2 > 0"
proof (rule ccontr)
  assume "\<not> (P^2 + Q^2 + R^2 > 0)"
  then have nonpos: "P^2 + Q^2 + R^2 \<le> 0" by simp
  have "P^2 \<ge> 0" "Q^2 \<ge> 0" "R^2 \<ge> 0" by simp_all
  with nonpos have "P^2 = 0" "Q^2 = 0" "R^2 = 0" by linarith+
  then have P0: "P = 0" and Q0: "Q = 0" and R0: "R = 0" by simp_all
  (* substitute P=Q=R=0 into th0 and d2 *)
  from th0 P0 Q0 R0 have e1: "Bc*k2 - Ac*s2 = 0" by simp
  from d2 P0 Q0 have e2: "-Bc*s2 - Ac*k2 = 0" by simp
  (* sum of squares identity *)
  have "(Bc*k2 - Ac*s2)^2 + (Bc*s2 + Ac*k2)^2 = (Ac^2 + Bc^2)*(k2^2 + s2^2)"
    by (simp add: power2_eq_square algebra_simps)
  moreover have "Bc*s2 + Ac*k2 = 0" using e2 by simp
  ultimately have "0 = (Ac^2 + Bc^2)*(k2^2 + s2^2)"
    using e1 by simp
  moreover have "k2^2 + s2^2 = 1" using pyth2 by (simp add: power2_eq_square)
  ultimately have "Ac^2 + Bc^2 = 0" by simp
  then have "Ac = 0 \<and> Bc = 0"
    by (simp only: sum_power2_eq_zero_iff)
  with kdiff show False by simp
qed

lemma disc_pos:
  fixes Ac Bc P Q R k2 s2 kk ss :: real
  assumes pyth2: "k2*k2 + s2*s2 = 1" and pyth1: "kk*kk + ss*ss = 1"
      and th0: "(Bc - P*kk)*k2 + (-Ac + Q*kk)*s2 + R*ss = 0"
      and d2:  "-(Bc - P*kk)*s2 + (-Ac + Q*kk)*k2 = 0"
      and d1:  "(P*ss)*k2 + (-Q*ss)*s2 + R*kk = 0"
      and ss_ne: "ss \<noteq> 0" and kdiff: "Ac \<noteq> 0 \<or> Bc \<noteq> 0"
  shows "(-(P*ss)*s2 + (-Q*ss)*k2)^2 - ((P*kk)*k2 + (-Q*kk)*s2 + (-R*ss)) * (-(Bc - P*kk)*k2 - (-Ac + Q*kk)*s2) > 0"
proof -
  have deteq: "((P*kk)*k2 + (-Q*kk)*s2 + (-R*ss)) * (-(Bc - P*kk)*k2 - (-Ac + Q*kk)*s2)
         - (-(P*ss)*s2 + (-Q*ss)*k2)^2
       = -(P^2 + Q^2 + R^2) * (ss^2)"
    using detH_indef_abstract[OF pyth2 pyth1 th0 d2 d1] .
  have gam: "P^2 + Q^2 + R^2 > 0"
    using gamma_pos[OF pyth2 th0 d2 ss_ne kdiff] .
  have "ss^2 > 0" using ss_ne by simp
  with gam have pos: "(P^2 + Q^2 + R^2) * (ss^2) > 0" by simp
  have disceq: "(-(P*ss)*s2 + (-Q*ss)*k2)^2 - ((P*kk)*k2 + (-Q*kk)*s2 + (-R*ss)) * (-(Bc - P*kk)*k2 - (-Ac + Q*kk)*s2)
       = (P^2 + Q^2 + R^2) * (ss^2)"
    using deteq by linarith
  show ?thesis using disceq pos by linarith
qed

end
