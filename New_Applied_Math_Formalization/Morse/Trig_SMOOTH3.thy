theory Trig_SMOOTH3
  imports "Applied_Math_Morse.Hadamard_2D"
begin

(* Abbreviations used in the comments / derivation:
     p1 = Bc*KZ + KY,  q1 = Ac*KZ + KX,  r1 = Ac*KY - Bc*KX,
     t  = \<omega>$1,  u = \<omega>$2.
   In all definitions below these are written out inline in terms of the
   five free real parameters Ac Bc KX KY KZ. *)

definition Theta_abs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real" where
  "Theta_abs Ac Bc KX KY KZ \<omega> =
     (Bc - (Bc*KZ + KY)*cos (\<omega>$1)) * cos (\<omega>$2)
   + (- Ac + (Ac*KZ + KX)*cos (\<omega>$1)) * sin (\<omega>$2)
   + (Ac*KY - Bc*KX) * sin (\<omega>$1)"

(* === First-order: gradient field G ===
     \<partial>\<^sub>1\<Theta> = p1*sin t*cos u - q1*sin t*sin u + r1*cos t
     \<partial>\<^sub>2\<Theta> = -(Bc - p1*cos t)*sin u + (-Ac + q1*cos t)*cos u           *)

definition Gabs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "Gabs Ac Bc KX KY KZ \<omega> = vector
     [ (Bc*KZ + KY) * sin (\<omega>$1) * cos (\<omega>$2)
         - (Ac*KZ + KX) * sin (\<omega>$1) * sin (\<omega>$2)
         + (Ac*KY - Bc*KX) * cos (\<omega>$1),
       - (Bc - (Bc*KZ + KY)*cos (\<omega>$1)) * sin (\<omega>$2)
         + (- Ac + (Ac*KZ + KX)*cos (\<omega>$1)) * cos (\<omega>$2) ]"

(* === Second-order: Hessian rows H1 = [\<partial>\<^sub>1\<^sub>1, \<partial>\<^sub>1\<^sub>2], H2 = [\<partial>\<^sub>1\<^sub>2, \<partial>\<^sub>2\<^sub>2] ===
     \<partial>\<^sub>1\<^sub>1\<Theta> = p1*cos t*cos u - q1*cos t*sin u - r1*sin t
     \<partial>\<^sub>1\<^sub>2\<Theta> = -p1*sin t*sin u - q1*sin t*cos u
     \<partial>\<^sub>2\<^sub>2\<Theta> = -(Bc - p1*cos t)*cos u - (-Ac + q1*cos t)*sin u            *)

definition H1abs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "H1abs Ac Bc KX KY KZ \<omega> = vector
     [ (Bc*KZ + KY) * cos (\<omega>$1) * cos (\<omega>$2)
         - (Ac*KZ + KX) * cos (\<omega>$1) * sin (\<omega>$2)
         - (Ac*KY - Bc*KX) * sin (\<omega>$1),
       - (Bc*KZ + KY) * sin (\<omega>$1) * sin (\<omega>$2)
         - (Ac*KZ + KX) * sin (\<omega>$1) * cos (\<omega>$2) ]"

definition H2abs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "H2abs Ac Bc KX KY KZ \<omega> = vector
     [ - (Bc*KZ + KY) * sin (\<omega>$1) * sin (\<omega>$2)
         - (Ac*KZ + KX) * sin (\<omega>$1) * cos (\<omega>$2),
       - (Bc - (Bc*KZ + KY)*cos (\<omega>$1)) * cos (\<omega>$2)
         - (- Ac + (Ac*KZ + KX)*cos (\<omega>$1)) * sin (\<omega>$2) ]"

(* === Third-order gradient fields K11 = grad(\<partial>\<^sub>1\<^sub>1\<Theta>), K12 = grad(\<partial>\<^sub>1\<^sub>2\<Theta>),
       K22 = grad(\<partial>\<^sub>2\<^sub>2\<Theta>) ===
   K11:  \<partial>\<^sub>1 = -p1*sin t*cos u + q1*sin t*sin u - r1*cos t
         \<partial>\<^sub>2 = -p1*cos t*sin u - q1*cos t*cos u
   K12:  \<partial>\<^sub>1 = -p1*cos t*sin u - q1*cos t*cos u
         \<partial>\<^sub>2 = -p1*sin t*cos u + q1*sin t*sin u
   K22 (h22 = -Bc*cos u + p1*cos t*cos u + Ac*sin u - q1*cos t*sin u):
         \<partial>\<^sub>1 = -p1*sin t*cos u + q1*sin t*sin u
         \<partial>\<^sub>2 = Bc*sin u - p1*cos t*sin u + Ac*cos u - q1*cos t*cos u        *)

definition K11abs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "K11abs Ac Bc KX KY KZ \<omega> = vector
     [ - (Bc*KZ + KY) * sin (\<omega>$1) * cos (\<omega>$2)
         + (Ac*KZ + KX) * sin (\<omega>$1) * sin (\<omega>$2)
         - (Ac*KY - Bc*KX) * cos (\<omega>$1),
       - (Bc*KZ + KY) * cos (\<omega>$1) * sin (\<omega>$2)
         - (Ac*KZ + KX) * cos (\<omega>$1) * cos (\<omega>$2) ]"

definition K12abs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "K12abs Ac Bc KX KY KZ \<omega> = vector
     [ - (Bc*KZ + KY) * cos (\<omega>$1) * sin (\<omega>$2)
         - (Ac*KZ + KX) * cos (\<omega>$1) * cos (\<omega>$2),
       - (Bc*KZ + KY) * sin (\<omega>$1) * cos (\<omega>$2)
         + (Ac*KZ + KX) * sin (\<omega>$1) * sin (\<omega>$2) ]"

definition K22abs :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real^2 \<Rightarrow> real^2" where
  "K22abs Ac Bc KX KY KZ \<omega> = vector
     [ - (Bc*KZ + KY) * sin (\<omega>$1) * cos (\<omega>$2)
         + (Ac*KZ + KX) * sin (\<omega>$1) * sin (\<omega>$2),
       Bc * sin (\<omega>$2) - (Bc*KZ + KY) * cos (\<omega>$1) * sin (\<omega>$2)
         + Ac * cos (\<omega>$2) - (Ac*KZ + KX) * cos (\<omega>$1) * cos (\<omega>$2) ]"

(* ============================================================= *)
(* has_derivative facts (technique from /tmp/kfield_scratch.thy)  *)
(* ============================================================= *)

lemma Theta_abs_has_derivative:
  fixes \<omega> :: "real^2"
  shows "(Theta_abs Ac Bc KX KY KZ has_derivative
            (\<lambda>h. inner (Gabs Ac Bc KX KY KZ \<omega>) h)) (at \<omega>)"
  unfolding Theta_abs_def Gabs_def
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
  apply (rule ext)
  apply (simp add: inner_vec_def sum_2 vector_2 algebra_simps)
  done

(* (G y)$1 = \<partial>\<^sub>1\<Theta>, its gradient is H1 = [\<partial>\<^sub>1\<^sub>1, \<partial>\<^sub>1\<^sub>2] *)
lemma G1_has_derivative:
  fixes \<omega> :: "real^2"
  shows "((\<lambda>y. (Gabs Ac Bc KX KY KZ y)$1) has_derivative
            (\<lambda>h. inner (H1abs Ac Bc KX KY KZ \<omega>) h)) (at \<omega>)"
  unfolding Gabs_def H1abs_def
  apply (simp only: vector_2)
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
  apply (rule ext)
  apply (simp add: inner_vec_def sum_2 vector_2 algebra_simps)
  done

(* (G y)$2 = \<partial>\<^sub>2\<Theta>, its gradient is H2 = [\<partial>\<^sub>1\<^sub>2, \<partial>\<^sub>2\<^sub>2] *)
lemma G2_has_derivative:
  fixes \<omega> :: "real^2"
  shows "((\<lambda>y. (Gabs Ac Bc KX KY KZ y)$2) has_derivative
            (\<lambda>h. inner (H2abs Ac Bc KX KY KZ \<omega>) h)) (at \<omega>)"
  unfolding Gabs_def H2abs_def
  apply (simp only: vector_2)
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
  apply (rule ext)
  apply (simp add: inner_vec_def sum_2 vector_2 algebra_simps)
  done

(* (H1 y)$1 = \<partial>\<^sub>1\<^sub>1\<Theta>, gradient K11 *)
lemma H1_1_has_derivative:
  fixes \<omega> :: "real^2"
  shows "((\<lambda>y. (H1abs Ac Bc KX KY KZ y)$1) has_derivative
            (\<lambda>h. inner (K11abs Ac Bc KX KY KZ \<omega>) h)) (at \<omega>)"
  unfolding H1abs_def K11abs_def
  apply (simp only: vector_2)
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
  apply (rule ext)
  apply (simp add: inner_vec_def sum_2 vector_2 algebra_simps)
  done

(* (H1 y)$2 = \<partial>\<^sub>1\<^sub>2\<Theta>, gradient K12 *)
lemma H1_2_has_derivative:
  fixes \<omega> :: "real^2"
  shows "((\<lambda>y. (H1abs Ac Bc KX KY KZ y)$2) has_derivative
            (\<lambda>h. inner (K12abs Ac Bc KX KY KZ \<omega>) h)) (at \<omega>)"
  unfolding H1abs_def K12abs_def
  apply (simp only: vector_2)
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
  apply (rule ext)
  apply (simp add: inner_vec_def sum_2 vector_2 algebra_simps)
  done

(* (H2 y)$2 = \<partial>\<^sub>2\<^sub>2\<Theta>, gradient K22 *)
lemma H2_2_has_derivative:
  fixes \<omega> :: "real^2"
  shows "((\<lambda>y. (H2abs Ac Bc KX KY KZ y)$2) has_derivative
            (\<lambda>h. inner (K22abs Ac Bc KX KY KZ \<omega>) h)) (at \<omega>)"
  unfolding H2abs_def K22abs_def
  apply (simp only: vector_2)
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros bounded_linear.has_derivative[OF bounded_linear_vec_nth])+
  apply (rule ext)
  apply (simp add: inner_vec_def sum_2 vector_2 algebra_simps)
  done

(* === Clairaut: (H1 \<omega>)$2 = (H2 \<omega>)$1 (both = \<partial>\<^sub>1\<^sub>2\<Theta>) === *)
lemma Clairaut_abs:
  fixes \<omega> :: "real^2"
  shows "(H1abs Ac Bc KX KY KZ \<omega>)$2 = (H2abs Ac Bc KX KY KZ \<omega>)$1"
  unfolding H1abs_def H2abs_def
  by (simp add: vector_2)

(* ============================================================= *)
(* Continuity facts                                              *)
(* ============================================================= *)

(* Scalar component continuity: (H1)$1, (H1)$2, (H2)$2 *)
lemma H1_1_continuous_on:
  "continuous_on S (\<lambda>x. (H1abs Ac Bc KX KY KZ x)$1)"
  unfolding H1abs_def
  apply (simp only: vector_2)
  by (auto intro!: continuous_intros
        continuous_on_compose2[OF _ linear_continuous_on[OF bounded_linear_vec_nth]])

lemma H1_2_continuous_on:
  "continuous_on S (\<lambda>x. (H1abs Ac Bc KX KY KZ x)$2)"
  unfolding H1abs_def
  by (simp only: vector_2, 
      simp only: continuous_intros
        continuous_on_compose2[OF _ linear_continuous_on[OF bounded_linear_vec_nth]])

lemma H2_2_continuous_on:
  "continuous_on S (\<lambda>x. (H2abs Ac Bc KX KY KZ x)$2)"
  unfolding H2abs_def
  by (simp only: vector_2,
      simp only: continuous_intros
        continuous_on_compose2[OF _ linear_continuous_on[OF bounded_linear_vec_nth]])

(* Vector-field continuity: K11, K12, K22 *)
lemma K11_continuous_on:
  "continuous_on S (K11abs Ac Bc KX KY KZ)"
  unfolding K11abs_def
  apply (subst vec_lambda_eta[symmetric])
  apply (rule continuous_on_vec_lambda)
  subgoal for i
    using exhaust_2[of i]
    apply (elim disjE)
     apply (simp_all add: vector_2)
     apply (auto intro!: continuous_intros
        continuous_on_compose2[OF _ linear_continuous_on[OF bounded_linear_vec_nth]])
    done
  done

lemma K12_continuous_on:
  "continuous_on S (K12abs Ac Bc KX KY KZ)"
  unfolding K12abs_def
  apply (subst vec_lambda_eta[symmetric])
  apply (rule continuous_on_vec_lambda)
  subgoal for i
    using exhaust_2[of i]
    apply (elim disjE)
     apply (simp_all add: vector_2)
     apply (auto intro!: continuous_intros
        continuous_on_compose2[OF _ linear_continuous_on[OF bounded_linear_vec_nth]])
    done
  done

lemma K22_continuous_on:
  "continuous_on S (K22abs Ac Bc KX KY KZ)"
  unfolding K22abs_def
  apply (subst vec_lambda_eta[symmetric])
  apply (rule continuous_on_vec_lambda)
  subgoal for i
    using exhaust_2[of i]
    apply (elim disjE)
     apply (simp_all add: vector_2)
     apply (auto intro!: continuous_intros
        continuous_on_compose2[OF _ linear_continuous_on[OF bounded_linear_vec_nth]])
    done
  done

(* ============================================================= *)
(* Main theorem                                                  *)
(* ============================================================= *)

lemma Theta_abs_SMOOTH3:
  "SMOOTH3 (Theta_abs Ac Bc KX KY KZ) (Gabs Ac Bc KX KY KZ)
           (H1abs Ac Bc KX KY KZ) (H2abs Ac Bc KX KY KZ)
           (K11abs Ac Bc KX KY KZ) (K12abs Ac Bc KX KY KZ)
           (K22abs Ac Bc KX KY KZ) S"
  unfolding SMOOTH3_def
  apply (intro conjI ballI)
            apply (rule Theta_abs_has_derivative)
           apply (rule G1_has_derivative)
          apply (rule G2_has_derivative)
         apply (rule Clairaut_abs)
        apply (rule H1_1_has_derivative)
       apply (rule H1_2_has_derivative)
      apply (rule H2_2_has_derivative)
     apply (rule H1_1_continuous_on)
    apply (rule H1_2_continuous_on)
   apply (rule H2_2_continuous_on)
    apply (rule K11_continuous_on)
   apply (rule K12_continuous_on)
  apply (rule K22_continuous_on)
  done

end
