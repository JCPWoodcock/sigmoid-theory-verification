theory DSSigmoid
  imports "HOL-Analysis.Analysis" Complex_Main
begin

definition sigmoid :: "real \<Rightarrow> real" where 
"sigmoid = (\<lambda> x::real. exp(x) / (1 + exp(x)))"

lemma sigmoid_alt_def: "sigmoid x = inverse (1 + exp(-x))"
  by (metis (no_types, opaque_lifting) div_by_1 divide_divide_eq_right divide_inverse_commute division_ring_inverse_add exp_minus exp_not_eq_zero sigmoid_def zero_neq_one)

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
  apply (smt (verit) divide_le_0_1_iff exp_gt_zero inverse_eq_divide sigmoid_alt_def)
  done

(* Prove that sigmoid(x) is strictly less than 1 for all x *)
lemma sigmoid_less_1: "sigmoid x < 1"
  apply (smt (verit) le_divide_eq_1_pos not_exp_le_zero sigmoid_def)
  done

(* Theorem: The sigmoid function takes values between 0 and 1 for all real x *)
theorem sigmoid_range: "0 < sigmoid x \<and> sigmoid x < 1"
  apply (simp add: sigmoid_less_1 sigmoid_pos)
  done

(* Symmetry (Odd Function)
The sigmoid function is symmetric about the origin in a certain sense:
\<sigma>(−x) = 1−\<sigma>(x). This property reflects the fact that as the input x becomes
negative, the sigmoid shifts its output towards 0, while positive inputs
shift the output towards 1. *)

theorem sigmoid_symmetry: "sigmoid (-x) = 1 - sigmoid x"
  apply (smt (verit, ccfv_SIG) add_divide_distrib divide_self_if exp_ge_zero inverse_eq_divide sigmoid_alt_def sigmoid_def)
  done

(* Sum Identity
The sigmoid function has an interesting identity when considering the sum of
sigmoid outputs for x and −x : \<sigma>(x) + \<sigma>(−x) = 1 This follows directly from
the symmetry property. *)

theorem "sigmoid(x) + sigmoid(-x) = 1"
  by (simp add: sigmoid_symmetry)

(* Increasing
The sigmoid function is strictly increasing. *)

theorem sigmoid_strictly_increasing: "x1 < x2 \<Longrightarrow> sigmoid x1 < sigmoid x2"
  apply (unfold sigmoid_alt_def)
  apply (smt (verit) add_strict_left_mono divide_eq_0_iff exp_gt_zero exp_less_cancel_iff inverse_less_iff_less le_divide_eq_1_pos neg_0_le_iff_le neg_le_iff_le order_less_trans real_add_le_0_iff)
  done

(* Derivative
The derivative of the sigmoid function can be expressed in terms of the function
itself: \<sigma>\<Zprime>(x) = \<sigma>(x ) \<^emph> (1 − \<sigma>(x )). This is a key identity used in
backpropagation for updating weights in neural networks. It shows that the
derivative depends on the value of the function itself, simplifying calculations
in optimisation problems. *)

lemma uminus_derive_minus_one: "(uminus has_derivative (*) (-1 :: real)) (at a within A)"
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros)
   apply (rule derivative_intros)
  apply fastforce
  done

lemma sigmod_derivative:
  "((\<lambda> x. sigmoid x) has_derivative (\<lambda> h. (sigmoid(x) * (1 - sigmoid(x))) * h)) (at x within A)"
  apply (unfold sigmoid_alt_def)
  apply (rule has_derivative_eq_rhs)
  apply (rule derivative_intros)
   apply (metis add.right_neutral le_minus_one_simps(1) minus_add_cancel not_exp_le_zero)
  apply (rule derivative_intros)
   apply (rule derivative_intros)
  apply (rule derivative_intros)
   apply (rule uminus_derive_minus_one)
  apply (auto simp add: fun_eq_iff)
  using division_ring_inverse_diff apply force
  done

(* Second Derivative
The second derivative of the sigmoid function can also be expressed in terms of
the function itself: \<sigma>\<Zprime>\<Zprime>(x) = \<sigma>(x)\<^emph>(1−\<sigma>(x))\<^emph>(1−2\<^emph>\<sigma>(x)). This identity is useful
when analysing the curvature of the sigmoid function, particularly in
optimisation problems. *)

(* Logit (Inverse of Sigmoid)
The inverse of the sigmoid function, often referred to as the logit function, is
given by: \<sigma>−1(y) = ln(y/1−y), for 0 < y < 1. This transformation converts a
probability (sigmoid output) back into the corresponding log-odds. *)

(* Multiplicative Scaling Property
For any constant c, the scaled sigmoid function \<sigma>(c \<^emph> x) can be related to \<sigma>(x)
through the following transformation: \<sigma>(cx) = 1. This shows how scaling the
input x affects 1+e−c\<^emph>x the shape of the sigmoid function, typically making it
steeper or flatter. *)

(* Addition of Two Sigmoids
There is no simple algebraic form for the sum of two sigmoids, but a useful
approximation for combining two sigmoid outputs \<sigma>(x1) and \<sigma>(x2) is via softmax
in multi-class classification settings.*)

(* Asymptotic Behaviour
As x \<rightarrow> +\<infinity>, the sigmoid function tends towards 1: lim_{x\<rightarrow>+\<infinity>} \<sigma>(x) = 1.
As x \<rightarrow> −\<infinity>, the sigmoid function tends towards 0: lim_{x\<rightarrow>-\<infinity>} \<sigma>(x) = 0. *)

term tendsto 
term at_top

term eventually

lemma tendsto_exp_neg_at_infinity:
  "\<forall>(\<epsilon> :: real) >0. \<exists>N. \<forall>x\<ge>N. abs (exp (-x)) < \<epsilon>"
proof (rule allI, rule impI)
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  show "\<exists>N. \<forall>x\<ge>N. \<bar>exp (- x)\<bar> < \<epsilon>"
  proof (cases "\<epsilon> \<le> 1")
    assume "\<epsilon> \<le> 1"
    show "\<exists>N. \<forall>x\<ge>N. \<bar>exp (- x)\<bar> < \<epsilon>"
      by (metis \<open>0 < \<epsilon>\<close> abs_exp_cancel dual_order.order_iff_strict exp_less_mono gt_ex ln_ge_iff minus_le_iff minus_less_iff order_le_less_trans)
  next
    assume "\<not> \<epsilon> \<le> 1"
    then have "1 < \<epsilon>"
      by simp 
    then show "\<exists>N. \<forall>x\<ge>N. \<bar>exp (- x)\<bar> < \<epsilon>"
      by (smt (verit, best) exp_gt_zero one_less_exp_iff)
  qed
qed

lemma tendsto_exp_neg_at_top: "((\<lambda>x. exp (-x)) \<longlongrightarrow> 0) at_top"
  unfolding  at_top_def principal_def Ball_def 
proof clarify
  fix S :: "'a set"
  assume zeroinS: "0 \<in> S"
  assume open_S: "open S"

(*
  obtain M where "\<forall>x. x > M \<longrightarrow> exp (-x) \<in> S"
  proof -
      have "\<forall>x. x  > - ln \<epsilon> \<longrightarrow> exp (-x) < \<epsilon>"
      proof (clarify)
        fix x 
        assume "x > - ln \<epsilon>"
        then have "-x <  ln \<epsilon>" by simp
        then have "exp (-x) < exp (ln \<epsilon>)" by blast
        then show "exp (-x) < \<epsilon>"
          by (simp add: \<open>0 < \<epsilon>\<close>)         
*)

  show "0 \<in> S \<Longrightarrow> \<forall>\<^sub>F x in at_top. exp (- x) \<in> S"


  
  qed








lemma tendsto_divide_approaches_const:
  fixes f g :: "real \<Rightarrow> real"
  assumes "((\<lambda>x. f x) \<longlongrightarrow> c) at_top"
      and "((\<lambda>x. g x) \<longlongrightarrow> \<infinity>) at_top"
      and "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) at_top"
proof -
  {
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    from \<open>((\<lambda>x. g x) \<longlongrightarrow> \<infinity>) at_top\<close> 
    obtain M1 where "\<forall>x \<ge> M1. g x > 0"
      by (smt (verit, best) 
          ereal_less(2)
          ereal_less(5)
          eventually_at_top_linorder
          order_tendstoD(1)) 
    from \<open>((\<lambda>x. f x) \<longlongrightarrow> c) at_top\<close>
    obtain M2 where "\<forall>x \<ge> M2. dist (f x) c < \<epsilon> / 2"
      by (simp add: tendsto_def)
    have "eventually (\<lambda>x. abs(f x / g x) < \<epsilon>) at_top"
      using \<open>g x \<longlongrightarrow> \<infinity>\<close> and \<open>f x \<longlongrightarrow> c\<close> by (auto simp: divide_less_iff)
  }
  thus ?thesis
    by (simp add: tendsto_def)
  oops

(* Prove that the limit of the sigmoid function as x \<rightarrow> +\<infinity> is 1 *)
lemma lim_sigmoid_infinity: "((\<lambda>x. sigmoid x) \<longlongrightarrow> 1) at_top"
proof -
  have "((\<lambda>x. exp (-x)) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_exp_neg_at_top)

  hence "((\<lambda>x. 1 / (1 + exp (-x))) \<longlongrightarrow> 1) at_top"
    by (rule tendsto_divide_approaches_const, simp_all)

  thus ?thesis
    by (simp add: sigmoid_def)
  oops

end

