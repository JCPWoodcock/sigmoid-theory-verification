theory Sigmoid
  imports "HOL-Analysis.Analysis" "HOL-Combinatorics.Stirling"  
begin

definition sigmoid :: "real \<Rightarrow> real" where 
"sigmoid = (\<lambda> x::real. exp(x) / (1 + exp(x)))"



lemma sigmoid_alt_def: "sigmoid x = inverse (1 + exp(-x))"
proof -
  have "sigmoid x = (exp(x) * exp(-x)) / ((1 + exp(x))* exp(-x))"
    unfolding sigmoid_def by simp
  also have "... = 1 / (1*exp(-x) + exp(x)*exp(-x))"
    by (simp add: distrib_right exp_minus_inverse)
  also have "... = inverse (exp(-x) + 1)"
    by (simp add: divide_inverse_commute exp_minus)
  finally show ?thesis
    by simp
qed

(* Bounds *)

lemma sigmoid_pos: "sigmoid x > 0"
  by (smt (verit) divide_le_0_1_iff exp_gt_zero inverse_eq_divide sigmoid_alt_def)

(* Prove that sigmoid(x) is strictly less than 1 for all x *)
lemma sigmoid_less_1: "sigmoid x < 1"
  by (smt (verit) le_divide_eq_1_pos not_exp_le_zero sigmoid_def)

(* Theorem: The sigmoid function takes values between 0 and 1 for all real x *)
theorem sigmoid_range: "0 < sigmoid x \<and> sigmoid x < 1"
  by (simp add: sigmoid_less_1 sigmoid_pos)






(* Symmetry (Odd Function)
The sigmoid function is symmetric about the origin in a certain sense:
\<sigma>(Ã\<cent>ÃÂÃÂx) = 1Ã\<cent>ÃÂÃÂ\<sigma>(x). This property reflects the fact that as the input x becomes
negative, the sigmoid shifts its output towards 0, while positive inputs
shift the output towards 1. *)

theorem sigmoid_symmetry: "sigmoid (-x) = 1 - sigmoid x"
  by (smt (verit, ccfv_SIG) add_divide_distrib divide_self_if 
      exp_ge_zero inverse_eq_divide sigmoid_alt_def sigmoid_def)


(* Sum Identity
The sigmoid function has an interesting identity when considering the sum of
sigmoid outputs for x and Ã\<cent>ÃÂÃÂx : \<sigma>(x) + \<sigma>(Ã\<cent>ÃÂÃÂx) = 1 This follows directly from
the symmetry property. *)

theorem "sigmoid(x) + sigmoid(-x) = 1"
  by (simp add: sigmoid_symmetry)

(* Increasing
The sigmoid function is strictly increasing. *)

theorem sigmoid_strictly_increasing: "x1 < x2 \<Longrightarrow> sigmoid x1 < sigmoid x2"
  by (unfold sigmoid_alt_def, 
      smt (verit) add_strict_left_mono divide_eq_0_iff exp_gt_zero exp_less_cancel_iff 
      inverse_less_iff_less le_divide_eq_1_pos neg_0_le_iff_le neg_le_iff_le order_less_trans real_add_le_0_iff)

lemma sigmoid_at_zero:
  "sigmoid 0 = 1/2"
  by (simp add: sigmoid_def)


lemma sigmoid_left_dom_range:
  assumes "x < 0"
  shows "sigmoid x < 1/2"
  by (metis assms sigmoid_at_zero sigmoid_strictly_increasing)


lemma sigmoid_right_dom_range:
  assumes "x > 0"
  shows "sigmoid x > 1/2"
  by (metis assms sigmoid_at_zero sigmoid_strictly_increasing)


(* Derivative
The derivative of the sigmoid function can be expressed in terms of the function
itself: \<sigma>\<Zprime>(x) = \<sigma>(x ) \<^emph> (1 Ã\<cent>ÃÂÃÂ \<sigma>(x )). This is a key identity used in
backpropagation for updating weights in neural networks. It shows that the
derivative depends on the value of the function itself, simplifying calculations
in optimisation problems. *)

lemma uminus_derive_minus_one: "(uminus has_derivative (*) (-1 :: real)) (at a within A)"
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros)
   apply (rule derivative_intros)
  apply fastforce
  done







lemma sigmoid_differentiable: 
  "(\<lambda>x. sigmoid x) differentiable_on UNIV"
proof -
  have "\<forall>x. sigmoid differentiable (at x)"
  proof 
    fix x :: real
    have num_diff: "(\<lambda>x. exp x) differentiable (at x)"
      by (simp add: field_differentiable_imp_differentiable field_differentiable_within_exp)
    have denom_diff: "(\<lambda>x. 1 + exp x) differentiable (at x)"
      by (simp add: num_diff)
    hence "(\<lambda>x. exp x / (1 + exp x)) differentiable (at x)"
      by (metis add_le_same_cancel2 num_diff differentiable_divide exp_ge_zero not_one_le_zero)    
    thus "sigmoid differentiable (at x)"
      by (simp add: sigmoid_def)
  qed
  thus ?thesis
    by (simp add: differentiable_on_def)
qed

lemma sigmoid_differentiable':
 "sigmoid field_differentiable at x"
  by (meson UNIV_I differentiable_on_def field_differentiable_def real_differentiableE sigmoid_differentiable)



lemma sigmoid_derivative:
  shows "deriv sigmoid x = sigmoid x * (1 - sigmoid x)"
  unfolding sigmoid_def
proof -    
  from field_differentiable_within_exp 
  have "deriv (\<lambda>x. exp x /(1 + exp x)) x = (deriv (\<lambda>x. exp x) x * (\<lambda>x. 1 + exp x) x - (\<lambda>x. exp x) x * deriv (\<lambda>x. 1 + exp x) x) / ((\<lambda>x. 1 + exp x) x)\<^sup>2"
    by(rule deriv_divide, 
       simp add: Derivative.field_differentiable_add field_differentiable_within_exp,
       smt (verit, ccfv_threshold) exp_gt_zero)
  also have "... = ((exp x) * (1 + exp x) -(exp x)* (deriv (\<lambda>w. ((\<lambda>v. 1)w + (\<lambda> u. exp u)w)) x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = ((exp x) * (1 + exp x) -(exp x) * (deriv (\<lambda>v. 1) x  + deriv (\<lambda> u. exp u) x)) / (1 + exp x)\<^sup>2"
    by (subst deriv_add, simp, simp add: field_differentiable_within_exp, auto)
  also have "... = ((exp x) * (1 + exp x) -(exp x)  * (exp x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = (exp x + (exp x)\<^sup>2 -(exp x)\<^sup>2) / (1 + exp x)\<^sup>2"
    by (simp add: ring_class.ring_distribs(1))  
  also have "... = (exp x / (1 + exp x))*(1 / (1 + exp x))"
    by (simp add: power2_eq_square)
  also have "... = exp x / (1 + exp x)*(1 - exp x / (1 + exp x))"
    by (metis add.inverse_inverse inverse_eq_divide sigmoid_alt_def sigmoid_def sigmoid_symmetry)
  finally show "deriv (\<lambda>x. exp x / (1 + exp x)) x = exp x / (1 + exp x) * (1 - exp x / (1 + exp x))".  
qed

lemma  sigmoid_derivative': "(sigmoid has_real_derivative (sigmoid x * (1 - sigmoid x))) (at x)"
  by (metis field_differentiable_derivI sigmoid_derivative sigmoid_differentiable')









(*This is simply helpful to have, but we can eliminate it if needed!*)
lemma deriv_one_minus_sigmoid:
  "deriv (\<lambda>y. 1 - sigmoid y) x = sigmoid x * (sigmoid x - 1)"
  apply (subst deriv_diff)
  apply simp
  using field_differentiable_def
  apply (metis UNIV_I differentiable_on_def real_differentiableE sigmoid_differentiable)
  by (metis deriv_const diff_0 minus_diff_eq mult_minus_right sigmoid_derivative)  





fun Nth_derivative :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real)" where
  "Nth_derivative 0 f = f " |
  "Nth_derivative (Suc n) f  = deriv (Nth_derivative n f)"

lemma first_derivative_alt_def:
 "Nth_derivative 1 f = deriv f"
  by simp

lemma second_derivative_alt_def:
"Nth_derivative 2 f  = deriv (deriv f)"
  by (simp add: numeral_2_eq_2)


definition C_k_on :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "C_k_on k f U \<equiv> open U \<and> (\<forall>n \<le> k. \<forall>x \<in> U. continuous_on U (Nth_derivative n f))"

definition smooth_on :: "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "smooth_on f U \<equiv> \<forall>k. C_k_on k f U"







(* Second Derivative
The second derivative of the sigmoid function can also be expressed in terms of
the function itself: \<sigma>\<Zprime>\<Zprime>(x) = \<sigma>(x)\<^emph>(1Ã\<cent>ÃÂÃÂ\<sigma>(x))\<^emph>(1Ã\<cent>ÃÂÃÂ2\<^emph>\<sigma>(x)). This identity is useful
when analysing the curvature of the sigmoid function, particularly in
optimisation problems. *)


lemma sigmoid_second_derivative:
  shows "Nth_derivative 2 sigmoid x = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)"
proof - 
  have "Nth_derivative 2 sigmoid x =  deriv ((\<lambda>w. deriv sigmoid w)) x"
    by (simp add: second_derivative_alt_def)
  also have "... = deriv ((\<lambda>w. (\<lambda>a. sigmoid a) w * (((\<lambda>u.1) - (\<lambda>v. sigmoid v)) w ))) x"
    by (simp add: sigmoid_derivative)
  also have "... = sigmoid x * (deriv ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x) + deriv (\<lambda>a. sigmoid a) x * ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x"
    by (rule deriv_mult,
        simp add: sigmoid_differentiable',
        simp add: Derivative.field_differentiable_diff sigmoid_differentiable')
  also have "... = sigmoid x * (deriv (\<lambda>y. 1 - sigmoid y) x) + deriv (\<lambda>a. sigmoid a) x * ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x"
    by (meson minus_apply)
  also have "... = sigmoid x * (deriv (\<lambda>y. 1 - sigmoid y) x) + deriv (\<lambda>a. sigmoid a) x * (\<lambda>y. 1 - sigmoid y) x"
    by simp
  also have "... = sigmoid x * sigmoid x * (sigmoid x -1) + sigmoid x * (1 - sigmoid x) * (1 - sigmoid x)"
    by (simp add: deriv_one_minus_sigmoid sigmoid_derivative)
  also have "... = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)"
    by (simp add: right_diff_distrib)
  finally show ?thesis.
qed





(*Reference: https://eecs.ceas.uc.edu/~minaiaa/papers/minai_sigmoids_NN93.pdf *)
(*           https://analyticphysics.com/Mathematical%20Methods/Multiple%20Derivatives%20of%20the%20Sigmoid%20Function.htm *)




(*Higher Order Derivatives*)


(*Stirling refers to Stirling numbers of the 2nd kind!*)

theorem nth_derivative_sigmoid:
  "\<And>x. Nth_derivative n sigmoid x = 
    (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
proof (induct n)
  case 0
  show ?case
    by simp
next
  fix n x
  assume induction_hypothesis: 
    "\<And>x. Nth_derivative n sigmoid x = 
         (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
  show "Nth_derivative (Suc n) sigmoid x = 
          (\<Sum>k = 1..(Suc n)+1. (-1)^(k+1) * fact (k - 1) * Stirling ((Suc n)+1) k * (sigmoid x)^k)"
  proof -
  
    
    (*Auxillary facts: *)

    have sigmoid_pwr_rule: "\<And>k. deriv (\<lambda>v. (sigmoid v)^k) x = k * (sigmoid x)^(k - 1) * deriv (\<lambda>u. sigmoid u) x"
        by (subst deriv_pow, simp add: sigmoid_differentiable', simp)
    have index_shift: "(\<Sum>j = 1..n+1. ((-1)^(j+1+1) * fact (j - 1) * Stirling (n+1) j * j * ((sigmoid x)^(j+1)))) = 
                          (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>j. j -1" "\<lambda>j. j + 1"], simp_all, auto)



    have simplified_terms: "(\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                                           ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)) = 
                            (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k *  (sigmoid x)^k))"
    proof - 
      have equal_terms: "\<forall> (k::nat) \<ge> 1.
       ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
       ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k) = 
       ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k * (sigmoid x)^k)"

      proof(clarify)
        fix k::nat
        assume "1 \<le> k"

        have "real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 1) k) * int k) * sigmoid x ^ k +
              real_of_int ((- 1) ^ (k + 1) * fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1)) * sigmoid x ^ k =
              real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                       (fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1))))) * sigmoid x ^ k"
          by (metis (mono_tags, opaque_lifting) ab_semigroup_mult_class.mult_ac(1) distrib_left mult.commute of_int_add)
        also have "... = real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                                  ((int (k - 1) * fact (k - 2)) * int (Stirling (n + 1) (k - 1)))))) * sigmoid x ^ k"
              by (simp add: ring_class.ring_distribs(1))
        also have "... = real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                                  (fact (k - 1) * int (Stirling (n + 1) (k - 1)))))) * sigmoid x ^ k"
          by (smt (verit, ccfv_threshold) Stirling.simps(3) add.commute diff_diff_left fact_num_eq_if mult_eq_0_iff of_nat_eq_0_iff one_add_one plus_1_eq_Suc)
        also have "... = real_of_int (((- 1) ^ (k + 1) * fact (k - 1)*
                              ( Stirling (n + 1) k *  k +    Stirling (n + 1) (k - 1)  )  )) * sigmoid x ^ k"
          by (simp add: distrib_left)
        also have "... = real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 2) k)) * sigmoid x ^ k"
          by (smt (z3) Stirling.simps(4) Suc_eq_plus1 \<open>1 \<le> k\<close> add.commute le_add_diff_inverse mult.commute nat_1_add_1 plus_nat.simps(2))
        finally show "real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 1) k) * int k) * sigmoid x ^ k +
         real_of_int ((- 1) ^ (k + 1) * fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1)) * sigmoid x ^ k =
         real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 2) k)) * sigmoid x ^ k".
      qed     
      from equal_terms show ?thesis
        by simp
    qed



    (*Main Goal: *)

    have "Nth_derivative (Suc n) sigmoid x = deriv (\<lambda> w. Nth_derivative n sigmoid w) x"
      by simp    
    also have "... = deriv (\<lambda> w.\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid w)^k) x"
      using induction_hypothesis by presburger
    also have "... = (\<Sum>k = 1..n+1. deriv (\<lambda>w. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid w)^k) x)"
      by (rule deriv_sum, metis(mono_tags) DERIV_chain2 DERIV_cmult_Id field_differentiable_def field_differentiable_power sigmoid_differentiable')
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * deriv (\<lambda>w. (sigmoid w)^k) x)"
      by(subst deriv_cmult, auto, simp add: field_differentiable_power sigmoid_differentiable')
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k - 1) * deriv (\<lambda>u. sigmoid u) x))"
      using sigmoid_pwr_rule by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k - 1) * (sigmoid x * (1 - sigmoid x))))"
      using sigmoid_derivative by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * ((sigmoid x)^(k - 1) * (sigmoid x)^1) * (1 - sigmoid x)))"
      by (simp add: mult.assoc)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k-1+1) * (1 - sigmoid x)))"
      by (metis (no_types, lifting) power_add)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k * (1  -sigmoid x)))"
      by fastforce
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (1 + -sigmoid x))"
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) *1 +
                                    ((    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x)))"
      by (meson vector_space_over_itself.scale_right_distrib)
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                                    (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))"
      by simp
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))"
      by (metis (no_types) sum.distrib)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * ((sigmoid x)^k * (-sigmoid x))))"
      by (simp add: mult.commute mult.left_commute)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>j = 1..n+1. ((-1)^(j+1+1) * fact (j - 1) * Stirling (n+1) j * j * ((sigmoid x)^(j+1))))"
      by (simp add: mult.commute)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) +
                     (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      using index_shift by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                      0 +
                     (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) of_int_mult of_int_of_nat_eq sum.cong)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k)  +
                                   ((-1)^(1+1) * fact (1 - 2) * Stirling (n+1) (1 - 1) * (1 - 1) * (sigmoid x)^1 ) +
                     (\<Sum>k = 2..n+2. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k - 1) * (k  -1) * (sigmoid x)^k )"
      by simp
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k)  +
                     (\<Sum>k = 1..n+2. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)"
      by (smt (verit) Suc_eq_plus1 Suc_leI add_Suc_shift add_cancel_left_left cancel_comm_monoid_add_class.diff_cancel nat_1_add_1 of_nat_0 sum.atLeast_Suc_atMost zero_less_Suc)
   also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                     (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k) +
               ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      by simp
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                                    ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)) +
                   ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      by (metis (no_types) sum.distrib)
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k *  (sigmoid x)^k)) +
                                    ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      using simplified_terms by presburger   
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k *  (sigmoid x)^k)) +
        (\<Sum>k = Suc n + 1..Suc n + 1.((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k  * (sigmoid x)^(k)))"
      by(subst atLeastAtMost_singleton,  simp)   
    also have "... = (\<Sum>k = 1..(Suc n)+1. (-1)^(k+1) * fact (k - 1) * Stirling ((Suc n)+1) k * (sigmoid x)^k)"
      by (subst sum.cong[where B="{1..n + 1}", where h = "\<lambda>k. ((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k  * (sigmoid x)^(k))"], simp_all)
    finally show ?thesis.
  qed
qed


corollary nth_derivative_sigmoid_differentiable:
  "Nth_derivative n sigmoid differentiable (at x)"
proof -
  have "(\<lambda>x. \<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)
   differentiable (at x)"
  proof - 
    have differentiable_terms: "\<And>k. 1 \<le> k \<and> k \<le> n+1 \<Longrightarrow> 
      (\<lambda>x. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k) differentiable (at x)"
    proof(clarify)
      fix k ::nat
      assume "1 \<le> k"
      assume " k \<le> n+1"
      show "(\<lambda>x. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k) differentiable (at x)"
        by (simp add: field_differentiable_imp_differentiable sigmoid_differentiable')
    qed
    then show ?thesis
      by(subst differentiable_sum,simp+)
  qed
  then show ?thesis
     using nth_derivative_sigmoid by presburger 
qed


corollary next_deriviative_sigmoid: "(Nth_derivative n  sigmoid has_real_derivative Nth_derivative (Suc n)  sigmoid x) (at x)"
  by (simp add: DERIV_deriv_iff_real_differentiable nth_derivative_sigmoid_differentiable)

corollary deriv_sigmoid_has_deriv: "(deriv sigmoid has_real_derivative deriv (deriv sigmoid) x) (at x)"
proof -
  have "\<forall>f. Nth_derivative (Suc 0) f = deriv f"
    using Nth_derivative.simps(1,2) by presburger
  then show ?thesis
    by (metis (no_types) DERIV_deriv_iff_real_differentiable nth_derivative_sigmoid_differentiable)
qed


lemma sigmoid_second_derivative':
  "(deriv sigmoid has_real_derivative (sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x))) (at x)"
  using deriv_sigmoid_has_deriv second_derivative_alt_def sigmoid_second_derivative by force



(*
(*A pair of basic facts about derivatives*)
lemma deriv_implies_has_real_derivative:
  "f differentiable (at x) \<and> deriv f x = g x \<Longrightarrow> (f has_real_derivative g x) (at x)"
  by (metis DERIV_deriv_iff_real_differentiable)


lemma has_real_derivative_implies_differentiable:
  "(f has_real_derivative g x) (at x) \<Longrightarrow> (f differentiable (at x)) \<and> ( deriv f x = g x) "
  using DERIV_imp_deriv real_differentiable_def by blast
*)




lemma smooth_sigmoid:
  "smooth_on sigmoid UNIV"
  unfolding smooth_on_def
  by (meson C_k_on_def has_real_derivative_imp_continuous_on next_deriviative_sigmoid open_UNIV)







(* Logit (Inverse of Sigmoid)
The inverse of the sigmoid function, often referred to as the logit function, is
given by: \<sigma>Ã\<cent>ÃÂÃÂ1(y) = ln(y/1Ã\<cent>ÃÂÃÂy), for 0 < y < 1. This transformation converts a
probability (sigmoid output) back into the corresponding log-odds. *)


definition logit :: "real \<Rightarrow> real" where
  "logit p = (if 0 < p \<and> p < 1 then ln (p / (1 - p)) else undefined)"


lemma sigmoid_logit_comp:
  "0 < p \<and> p < 1 \<Longrightarrow> sigmoid (logit p) = p"
proof -
  assume "0 < p \<and> p < 1"
  then show "sigmoid (logit p ) = p"
    by (smt (verit, del_insts) divide_pos_pos exp_ln_iff logit_def real_shrink_Galois sigmoid_def)
qed


lemma logit_sigmoid_comp:
  "logit (sigmoid p ) = p"
  by (smt (verit, best) sigmoid_less_1 sigmoid_logit_comp sigmoid_pos sigmoid_strictly_increasing)


definition softmax :: "real^'k \<Rightarrow> real^'k" where 
"softmax z = (\<chi> i. exp (z $ i) / (\<Sum> j\<in>UNIV. exp (z $ j)))"  


lemma tanh_sigmoid_relationship:
  "2 * sigmoid (2 * x) - 1 = tanh x"
proof -
  have "2 * sigmoid (2 * x) - 1 = 2 * (1 / (1 + exp (- (2 * x)))) - 1"
    by (simp add: inverse_eq_divide sigmoid_alt_def)
  also have "... = (2 / (1 + exp (- (2 * x)))) - 1"
    by simp
  also have "... = (2 - (1 + exp (- (2 * x)))) / (1 + exp (- (2 * x)))"
    by (smt (verit, ccfv_SIG) diff_divide_distrib div_self exp_gt_zero)
  also have "... = (exp x * (exp x - exp (-x))) / (exp x * (exp x + exp (-x)))"
    by (smt (z3) exp_not_eq_zero mult_divide_mult_cancel_left_if tanh_altdef tanh_real_altdef)
  also have "... = (exp x - exp (-x)) / (exp x + exp (-x))"
    using exp_gt_zero by simp
  also have "... = tanh x"
    by (simp add: tanh_altdef)
  finally show ?thesis.
qed





lemma tendsto_at_top_epsilon_def:
  "(f \<longlongrightarrow> L) at_top = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<ge> N. \<bar>(f (x::real)::real) - L\<bar> < \<epsilon>)"
    by (simp add: Zfun_def tendsto_Zfun_iff eventually_at_top_linorder)

lemma tendsto_at_bot_epsilon_def:
  "(f \<longlongrightarrow> L) at_bot = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<le> N. \<bar>(f (x::real)::real) - L\<bar> < \<epsilon>)"
    by (simp add: Zfun_def tendsto_Zfun_iff eventually_at_bot_linorder)

lemma tendsto_inf_at_top_epsilon_def:
  "(g \<longlongrightarrow> \<infinity>) at_top = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<ge> N. (g (x::real)::real) > \<epsilon>)"
  by (subst tendsto_PInfty', subst Filter.eventually_at_top_linorder, simp)
  
lemma tendsto_inf_at_bot_epsilon_def:
  "(g \<longlongrightarrow> \<infinity>) at_bot = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<le> N. (g (x::real)::real) > \<epsilon>)"
  by (subst tendsto_PInfty', subst Filter.eventually_at_bot_linorder, simp)

lemma tendsto_minus_inf_at_top_epsilon_def:
  "(g \<longlongrightarrow> -\<infinity>) at_top = (\<forall> \<epsilon> < 0. \<exists>N. \<forall>x \<ge> N. (g (x::real)::real) < \<epsilon>)"
  by(subst tendsto_MInfty', subst Filter.eventually_at_top_linorder, simp)

lemma tendsto_minus_inf_at_bot_epsilon_def:
  "(g \<longlongrightarrow> -\<infinity>) at_bot = (\<forall> \<epsilon> < 0. \<exists>N. \<forall>x \<le> N. (g (x::real)::real) < \<epsilon>)"
  by (subst tendsto_MInfty', subst Filter.eventually_at_bot_linorder, simp)






lemma tendsto_exp_neg_at_infinity: "((\<lambda>(x :: real). exp (-x)) \<longlongrightarrow> 0) at_top"
  by(subst tendsto_at_top_epsilon_def, metis abs_exp_cancel abs_minus_cancel abs_minus_commute 
     diff_0 exp_less_mono exp_ln_iff gt_ex minus_le_iff minus_less_iff order_le_less_trans)

 


lemma tendsto_divide_approaches_const:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim:"((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_top"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_top"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_top"
proof(subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  obtain M where M_def: "M = abs c + 1" and M_gt_0: "M > 0"
    by simp

  obtain N1 where N1_def: "\<forall>x\<ge>N1. abs (f x - c) < 1"
    using f_lim tendsto_at_top_epsilon_def zero_less_one by blast 

  have f_bound: "\<forall>x\<ge>N1. abs (f x) < M"
    using M_def N1_def by fastforce

  have M_over_\<epsilon>_gt_0: "M / \<epsilon> > 0"
    by (simp add: M_gt_0 \<epsilon>_pos)

  then obtain N2 where N2_def: "\<forall>x\<ge>N2. g x > M / \<epsilon>"
    using g_lim tendsto_inf_at_top_epsilon_def by blast

  obtain N where "N = max N1 N2" and N_ge_N1: "N \<ge> N1" and N_ge_N2: "N \<ge> N2"
    by auto 
    
  show "\<exists>N::real. \<forall>x\<ge>N. \<bar>f x / g x - 0\<bar> < \<epsilon>"
  proof(intro exI [where x=N], clarify)
    fix x :: real
    assume x_ge_N: " N \<le> x"

    have f_bound_x: "\<bar>f x\<bar> < M"
      using N_ge_N1 f_bound x_ge_N by auto

    have g_bound_x: "g x > M / \<epsilon>"
      using N2_def N_ge_N2 x_ge_N by auto 

    have "\<bar>f x / g x\<bar> = \<bar>f x\<bar> / \<bar>g x\<bar>"
      using abs_divide by blast
    also have "... < M /  \<bar>g x\<bar>"
      using M_over_\<epsilon>_gt_0 divide_strict_right_mono f_bound_x g_bound_x by force
    also have  "... < \<epsilon>"
      by (metis  M_over_\<epsilon>_gt_0 \<epsilon>_pos abs_real_def g_bound_x mult.commute order_less_irrefl order_less_trans pos_divide_less_eq)
    finally show "\<bar>f x / g x - 0\<bar> < \<epsilon>"
      by linarith
  qed      
qed

lemma tendsto_divide_approaches_const_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim: "((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_bot"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_bot"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_bot"
proof(subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  obtain M where M_def: "M = abs c + 1" and M_gt_0: "M > 0"
    by simp

  obtain N1 where N1_def: "\<forall>x\<le>N1. abs (f x - c) < 1"
    using f_lim tendsto_at_bot_epsilon_def zero_less_one by blast 

  have f_bound: "\<forall>x\<le>N1. abs (f x) < M"
    using M_def N1_def by fastforce

  have M_over_\<epsilon>_gt_0: "M / \<epsilon> > 0"
    by (simp add: M_gt_0 \<epsilon>_pos)

  then obtain N2 where N2_def: "\<forall>x\<le>N2. g x > M / \<epsilon>"
    using g_lim tendsto_inf_at_bot_epsilon_def by blast

  obtain N where "N = min N1 N2" and N_le_N1: "N \<le> N1" and N_le_N2: "N \<le> N2"
    by auto 
    
  show "\<exists>N::real. \<forall>x\<le>N. \<bar>f x / g x - 0\<bar> < \<epsilon>"
  proof(intro exI [where x=N], clarify)
    fix x :: real
    assume x_le_N: "x \<le> N"

    have f_bound_x: "\<bar>f x\<bar> < M"
      using N_le_N1 f_bound x_le_N by auto

    have g_bound_x: "g x > M / \<epsilon>"
      using N2_def N_le_N2 x_le_N by auto 

    have "\<bar>f x / g x\<bar> = \<bar>f x\<bar> / \<bar>g x\<bar>"
      using abs_divide by blast
    also have "... < M /  \<bar>g x\<bar>"
      using M_over_\<epsilon>_gt_0 divide_strict_right_mono f_bound_x g_bound_x by force
    also have  "... < \<epsilon>"
      by (metis  M_over_\<epsilon>_gt_0 \<epsilon>_pos abs_real_def g_bound_x mult.commute order_less_irrefl order_less_trans pos_divide_less_eq)
    finally show "\<bar>f x / g x - 0\<bar> < \<epsilon>"
      by linarith
  qed      
qed






(* Asymptotic Behaviour
As x \<rightarrow> +\<infinity>, the sigmoid function tends towards 1: lim_{x\<rightarrow>+\<infinity>} \<sigma>(x) = 1.
As x \<rightarrow> Ã\<cent>ÃÂÃÂ\<infinity>, the sigmoid function tends towards 0: lim_{x\<rightarrow>-\<infinity>} \<sigma>(x) = 0. *)

(* Proof that the limit of the sigmoid function as x \<rightarrow> +\<infinity> is 1 *)
lemma lim_sigmoid_infinity: "((\<lambda>x. sigmoid x) \<longlongrightarrow> 1) at_top"
proof(subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  then obtain N where N_def: "\<forall>x \<ge> N. exp (- x) < \<epsilon>"
    by (metis dual_order.trans exp_le_cancel_iff exp_ln gt_ex le_minus_iff linorder_not_less)
    
  have "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> \<le> exp (-x)"
    by (smt(verit, best) divide_inverse exp_gt_zero exp_minus_inverse
        mult_le_cancel_left_pos sigmoid_alt_def sigmoid_def sigmoid_symmetry)

  then have "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon>"
    by (meson N_def order_le_less_trans)
  then show "\<exists>N. \<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon>"
    by blast
qed



(* Proof that the limit of the sigmoid function as x \<rightarrow> -\<infinity> is 0 *)
lemma lim_sigmoid_minus_infinity: "(sigmoid \<longlongrightarrow> 0) at_bot"
proof (subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"
  
  have "\<forall>x \<le> ln \<epsilon>. \<bar>sigmoid x - 0\<bar> < \<epsilon>"
  proof(clarify)
    fix x :: real
    assume "x \<le> ln \<epsilon>"
    then have "-x \<ge> - ln \<epsilon>"
      by simp
    then have f1: "exp (- x) \<ge> exp (- ln \<epsilon>)"
      by simp
    have "exp (- ln \<epsilon>) = 1 / \<epsilon>"
      by (simp add: \<epsilon>_pos exp_minus inverse_eq_divide)
    then have "1 + exp (- x) \<ge>  1 / \<epsilon>"
      using f1 by auto
    then have "sigmoid x \<le> \<epsilon>"
       using \<epsilon>_pos le_imp_inverse_le sigmoid_alt_def by fastforce 
    then show "\<bar>sigmoid x - 0\<bar> < \<epsilon>"
      by (smt (verit, best) exp_ln exp_minus f1 inverse_inverse_eq sigmoid_alt_def sigmoid_pos)
  qed
  then show "\<exists>N::real. \<forall>x\<le>N. \<bar>sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (rule exI[where x="ln \<epsilon>"])
qed










(*Limits of Derivative *)


lemma sig_deriv_lim_at_top: "(deriv sigmoid \<longlongrightarrow> 0) at_top"
proof (subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  (* Using the fact that sigmoid(x) \<longrightarrow> 1 as x \<longrightarrow> \<infinity> *)
  obtain N where N_def: "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon> / 2"
    using lim_sigmoid_infinity[unfolded tendsto_at_top_epsilon_def] \<epsilon>_pos
    by (metis  half_gt_zero)



  have deriv_bound: "\<forall>x \<ge> N. \<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>"
  proof (clarify)
    fix x
    assume "x \<ge> N"
    hence "\<bar>deriv sigmoid x\<bar> = \<bar>sigmoid x - 1 + 1\<bar> * \<bar>1 - sigmoid x\<bar>"
      by (simp add: abs_mult sigmoid_derivative)

    also have "... \<le> \<bar>sigmoid x - 1\<bar>"
      by (smt (verit) mult_cancel_right1 mult_right_mono sigmoid_range)
    finally show "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>".      
  qed

  have "\<forall>x \<ge> N. \<bar>deriv sigmoid x\<bar> < \<epsilon>"
  proof (clarify)
    fix x
    assume "x \<ge> N"
    hence "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>"
      using deriv_bound by simp
    also have "... < \<epsilon> / 2"
      using `x \<ge> N` N_def by simp
    also have "... < \<epsilon>"
      using \<epsilon>_pos by simp
    finally show "\<bar>deriv sigmoid x\<bar> < \<epsilon>" .
  qed

  then show "\<exists>N::real. \<forall>x\<ge>N. \<bar>deriv sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (metis diff_zero)
qed

lemma sig_deriv_lim_at_bot: "(deriv sigmoid \<longlongrightarrow> 0) at_bot"
proof (subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  (* Using the fact that sigmoid(x) \<longrightarrow> 0 as x \<longrightarrow>  -\<infinity> *)
  obtain N where N_def: "\<forall>x \<le> N. \<bar>sigmoid x - 0\<bar> < \<epsilon> / 2"
    using lim_sigmoid_minus_infinity[unfolded tendsto_at_bot_epsilon_def] \<epsilon>_pos
    by (meson half_gt_zero)

  have deriv_bound: "\<forall>x \<le> N. \<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>"
  proof (clarify)
    fix x
    assume "x \<le> N"
    hence "\<bar>deriv sigmoid x\<bar> = \<bar>sigmoid x - 0 + 0\<bar> * \<bar>1 - sigmoid x\<bar>"
      by (simp add: abs_mult sigmoid_derivative)
    also have "... \<le> \<bar>sigmoid x - 0\<bar>"
      by (smt (verit, del_insts) mult_cancel_left2 mult_left_mono sigmoid_range)
    finally show "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>".
  qed

  have "\<forall>x \<le> N. \<bar>deriv sigmoid x\<bar> < \<epsilon>"
  proof (clarify)
    fix x
    assume "x \<le> N"
    hence "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>"
      using deriv_bound by simp
    also have "... < \<epsilon> / 2"
      using `x \<le> N` N_def by simp
    also have "... < \<epsilon>"
      using \<epsilon>_pos by simp
    finally show "\<bar>deriv sigmoid x\<bar> < \<epsilon>".
  qed

  then show "\<exists>N::real. \<forall>x \<le> N. \<bar>deriv sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (metis diff_zero)
qed











(*Values of second derivative *)

lemma second_derivative_sigmoid_positive_on:
  assumes "x < 0"
  shows "Nth_derivative 2 sigmoid x > 0"
proof -
  have "1 - 2 * sigmoid x > 0"
    using assms sigmoid_left_dom_range by force
  then show "Nth_derivative 2 sigmoid x > 0"
    by (simp add: sigmoid_range sigmoid_second_derivative)
qed


lemma second_derivative_sigmoid_negative_on:
  assumes "x > 0"
  shows "Nth_derivative 2 sigmoid x < 0"
proof -
  have "1 - 2 * sigmoid x < 0"
    by (smt (verit) assms sigmoid_strictly_increasing sigmoid_symmetry)
  then show "Nth_derivative 2 sigmoid x < 0"
    by (simp add: mult_pos_neg sigmoid_range sigmoid_second_derivative)
qed

lemma sigmoid_inflection_point:
  "Nth_derivative 2 sigmoid 0 = 0"
  by (simp add: sigmoid_alt_def sigmoid_second_derivative)



(*Values of Derivative*)

lemma sigmoid_positive_derivative:
"deriv sigmoid x > 0"
  by (simp add: sigmoid_derivative sigmoid_range)

lemma sigmoid_deriv_0:
"deriv sigmoid 0 = 1/4"
proof -
  have f1: "1 / (1 + 1) = sigmoid 0"
    by (simp add: sigmoid_def)
  then have f2: "\<forall>r. sigmoid 0 * (r + r) = r"
    by simp
  then have f3: "\<forall>n. sigmoid 0 * numeral (num.Bit0 n) = numeral n"
    by (metis (no_types) numeral_Bit0)
  have f4: "\<forall>r. sigmoid r * sigmoid (- r) = deriv sigmoid r"
    using sigmoid_derivative sigmoid_symmetry by presburger
  have "sigmoid 0 = 0 \<longrightarrow> deriv sigmoid 0 = 1 / 4"
    using f1 by force
  then show ?thesis
    using f4 f3 f2 by (metis (no_types) add.inverse_neutral divide_divide_eq_right nonzero_mult_div_cancel_left one_add_one zero_neq_numeral)
qed

lemma deriv_sigmoid_increase_on_negatives:
  assumes "x2 < 0"
  assumes "x1 < x2" 
  shows "deriv sigmoid x1 < deriv sigmoid x2"
  by(rule DERIV_pos_imp_increasing, simp add: assms(2), metis assms(1) deriv_sigmoid_has_deriv 
          dual_order.strict_trans linorder_not_le nle_le second_derivative_alt_def second_derivative_sigmoid_positive_on)
  



lemma deriv_sigmoid_decreases_on_positives:
  assumes "0 < x1"
  assumes "x1 < x2" 
  shows "deriv sigmoid x2 < deriv sigmoid x1"
  by(rule DERIV_neg_imp_decreasing, simp add: assms(2), metis assms(1) deriv_sigmoid_has_deriv 
          dual_order.strict_trans linorder_not_le nle_le second_derivative_alt_def second_derivative_sigmoid_negative_on)



lemma sigmoid_derivative_upper_bound:
  assumes "x\<noteq> 0"
  shows "deriv sigmoid x < 1/4"
proof(cases "x \<le> 0")
  assume "x\<le>0"
  then have neg_case: "x < 0"
    using assms by linarith
  then have "deriv sigmoid x < deriv sigmoid 0"
  proof(rule DERIV_pos_imp_increasing_open)
    show "\<And>xa::real. x < xa \<Longrightarrow> xa < 0 \<Longrightarrow> \<exists>y::real. (deriv sigmoid has_real_derivative y) (at xa) \<and> 0 < y"
      by (metis (no_types) deriv_sigmoid_has_deriv second_derivative_alt_def second_derivative_sigmoid_positive_on)
    show "continuous_on {x..0::real} (deriv sigmoid)"
      by (meson DERIV_atLeastAtMost_imp_continuous_on deriv_sigmoid_has_deriv)
  qed
  then show "deriv sigmoid x < 1/4"
    by (simp add: sigmoid_deriv_0)
next
  assume "\<not> x \<le> 0"
  then have "0 < x"
    by linarith
  then have "deriv sigmoid x < deriv sigmoid 0"
  proof(rule DERIV_neg_imp_decreasing_open)
    show "\<And>xa::real. 0 < xa \<Longrightarrow> xa < x \<Longrightarrow> \<exists>y::real. (deriv sigmoid has_real_derivative y) (at xa) \<and> y < 0"
      by (metis (no_types) deriv_sigmoid_has_deriv second_derivative_alt_def second_derivative_sigmoid_negative_on)
    show "continuous_on {0..x::real} (deriv sigmoid)"
      by (meson DERIV_atLeastAtMost_imp_continuous_on deriv_sigmoid_has_deriv)
  qed
  then show "deriv sigmoid x < 1/4"
    by (simp add: sigmoid_deriv_0)
qed







theorem sigmoid_derivative_range:
  "0 < deriv sigmoid x \<and> deriv sigmoid x \<le> 1/4"
  by (smt (verit, best) sigmoid_deriv_0 sigmoid_derivative_upper_bound sigmoid_positive_derivative)








(*Smooth : Every derivative exists and is continuous.
           Every derivative exists.  f^(n) is differentiable for every n
Analytic: A function is equal to its Taylor series about each point
*)


(*  Is this what I want to state it as?  What about for the higher derivatives?
lemma sigmoid_is_contin_differentiable: "continuous_on \<real> (deriv sigmoid)"
*)







(*Sigmoidal Definition and Properties of Such Functions*)

definition sigmoidal :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "sigmoidal f \<equiv> (f \<longlongrightarrow> 1) at_top \<and> (f \<longlongrightarrow> 0) at_bot"


lemma sigmoid_is_sigmoidal: "sigmoidal sigmoid"
  unfolding sigmoidal_def
  by (simp add: lim_sigmoid_infinity lim_sigmoid_minus_infinity)



definition heaviside :: "real \<Rightarrow> real" where
  "heaviside x = (if x < 0 then 0 else 1)"

lemma heaviside_right: "x \<ge> 0 \<Longrightarrow> heaviside x = 1"
  by (simp add: heaviside_def)

lemma heaviside_left: "x < 0 \<Longrightarrow> heaviside x = 0"
  by (simp add: heaviside_def)

lemma heaviside_mono: "x < y \<Longrightarrow> heaviside x \<le> heaviside y"
  by (simp add: heaviside_def)

lemma heaviside_limit_neg_infinity:
  "(heaviside \<longlongrightarrow> 0) at_bot"
  by(rule tendsto_eventually, subst eventually_at_bot_dense, meson heaviside_def)

lemma heaviside_limit_pos_infinity:
  "(heaviside \<longlongrightarrow> 1) at_top"
  by(rule tendsto_eventually, subst eventually_at_top_dense, meson heaviside_def order.asym) 

lemma heaviside_is_sigmoidal: "sigmoidal heaviside"
  by (simp add: heaviside_limit_neg_infinity heaviside_limit_pos_infinity sigmoidal_def)




lemma equal_limits_diff_zero_at_top:
  assumes f_lim: "(f \<longlongrightarrow> (L1::real)) at_top"
  assumes g_lim: "(g \<longlongrightarrow> (L2::real)) at_top"
  shows "((f - g) \<longlongrightarrow> (L1 - L2)) at_top"
proof -
  have "((\<lambda>x. f x - g x) \<longlongrightarrow> L1 - L2) at_top"
    by (rule tendsto_diff, rule f_lim, rule g_lim)
  then show ?thesis 
    by (simp add: fun_diff_def)
qed

lemma equal_limits_diff_zero_at_bot:
  assumes f_lim: "(f \<longlongrightarrow> (L1::real)) at_bot"
  assumes g_lim: "(g \<longlongrightarrow> (L2::real)) at_bot"
  shows "((f - g) \<longlongrightarrow> (L1 - L2)) at_bot"
proof -
  have "((\<lambda>x. f x - g x) \<longlongrightarrow> L1 - L2) at_bot"
    by (rule tendsto_diff, rule f_lim, rule g_lim)
  then show ?thesis 
    by (simp add: fun_diff_def)
qed








lemma sigmoidal_uniform_approximation:  
  assumes "sigmoidal \<sigma>"
  assumes "(\<epsilon> :: real) > 0" and "(h :: real) > 0"    
  shows "\<exists>(\<omega>::real)>0. \<forall>w\<ge>\<omega>. \<forall>k<length (xs :: real list).
           (\<forall>x. x - xs!k \<ge> h   \<longrightarrow> \<bar>\<sigma> (w * (x - xs!k)) - 1\<bar> < \<epsilon>) \<and>
           (\<forall>x. x - xs!k \<le> -h  \<longrightarrow> \<bar>\<sigma> (w * (x - xs!k))\<bar> < \<epsilon>)"
proof -
  (* Use the sigmoidal assumption to extract limits at_top and at_bot *)
  have lim_at_top: "(\<sigma> \<longlongrightarrow> 1) at_top"
    using assms(1) unfolding sigmoidal_def by simp
  then obtain Ntop where Ntop_def: "\<forall>x \<ge> Ntop. \<bar>\<sigma> x - 1\<bar> < \<epsilon>"
    using assms(2) tendsto_at_top_epsilon_def by blast

  have lim_at_bot: "(\<sigma> \<longlongrightarrow> 0) at_bot"
    using assms(1) unfolding sigmoidal_def by simp
  then obtain Nbot where Nbot_def: "\<forall>x \<le> Nbot. \<bar>\<sigma> x\<bar> < \<epsilon>"
    using assms(2) tendsto_at_bot_epsilon_def by fastforce

  (* Define \<omega> to control the approximation *)
  obtain  \<omega> where \<omega>_def: "\<omega> = max (max 1 (Ntop / h)) (-Nbot / h)"
    by blast
  then have \<omega>_pos: "0 < \<omega>" using assms(2) by simp

  (* Show that \<omega> satisfies the required property *)
  show ?thesis
  proof (intro exI[where x = \<omega>] allI impI conjI insert \<omega>_pos)
    fix w :: real and k :: nat and x :: real
    assume w_ge_\<omega>: "\<omega> \<le> w"
    assume k_bound: "k < length xs"

    (* Case 1: x - xs!k \<ge> h *)
    have "w * h \<ge> Ntop"
      using \<omega>_def assms(3) pos_divide_le_eq w_ge_\<omega> by auto

    then show "x - xs!k \<ge> h \<Longrightarrow> \<bar>\<sigma> (w * (x - xs!k)) - 1\<bar> < \<epsilon>"
      using Ntop_def
      by (smt (verit) \<omega>_pos mult_less_cancel_left w_ge_\<omega>)

    (* Case 2: x - xs!k \<le> -h *)
    have "-w * h \<le> Nbot"
      using \<omega>_def assms(3) pos_divide_le_eq w_ge_\<omega>
      by (smt (verit, ccfv_SIG) mult_minus_left) 
    then show "x - xs!k \<le> -h \<Longrightarrow> \<bar>\<sigma> (w * (x - xs!k))\<bar> < \<epsilon>"
      using Nbot_def
      by (smt (verit, best) \<omega>_pos minus_mult_minus mult_less_cancel_left w_ge_\<omega>)
  qed
qed

end