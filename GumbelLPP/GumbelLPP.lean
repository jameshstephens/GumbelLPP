-- Core Analysis: Exp, Log, Derivatives, and Convexity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue

-- Tactics used in the proof
import Mathlib.Tactic.Linarith    -- For nlinarith
import Mathlib.Tactic.FieldSimp   -- For field_simp
import Mathlib.Tactic.FunProp     -- For fun_prop
import Mathlib.Tactic.GCongr      -- For gcongr
import Mathlib.Tactic.Ring        -- For ring/ring_nf
import Mathlib.Tactic.NormNum     -- For norm_num
import Mathlib.Tactic.Positivity  -- For positivity
import Aesop                      -- For aesop

-- Unused scopes in this specific snippet (Uncomment if needed)
-- import Mathlib.Algebra.BigOperators.Group.Finset -- For open scoped BigOperators
-- import Mathlib.Data.Set.Pointwise.Basic          -- For open scoped Pointwise

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of the function h_N(x) used in the coupling.
-/
noncomputable def h (N : ℝ) (x : ℝ) : ℝ :=
  - Real.log (N * (1 - Real.exp (-Real.exp (-x) / N))) - x

/--
Lemma 1: Convexity and bounds for h_N(x).
-/
theorem lemma_1 (N : ℝ) (hN : 1 ≤ N) :
    ConvexOn ℝ Set.univ (h N) ∧
    (∀ x, 0 < h N x ∧ h N x ≤ Real.exp (-x) / N) ∧
    (∀ x, 0 < x → Real.exp (-x) / (3 * N) ≤ h N x) := by
      unfold ConvexOn h;
      refine' ⟨ _, _, _ ⟩;
      · -- We'll use the fact that $h_N(x)$ is the composition of convex functions.
        have h_convex : ConvexOn ℝ Set.univ (fun x => -Real.log (1 - Real.exp (-Real.exp (-x) / N))) := by
          apply_rules [ convexOn_of_deriv2_nonneg, convex_univ ];
          · field_simp;
            exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.neg <| ContinuousAt.log ( continuousAt_const.sub <| Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg <| ContinuousAt.div_const ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg continuousAt_id ) _ ) <| ne_of_gt <| sub_pos_of_lt <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr <| by positivity;
          · field_simp;
            exact DifferentiableOn.neg ( DifferentiableOn.log ( DifferentiableOn.sub ( differentiableOn_const _ ) ( DifferentiableOn.exp ( DifferentiableOn.neg ( DifferentiableOn.div_const ( DifferentiableOn.exp ( differentiableOn_id.neg ) ) _ ) ) ) ) fun x hx => ne_of_gt ( sub_pos.mpr ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr ( by positivity ) ) ) ) );
          · refine' DifferentiableOn.congr _ _;
            use fun x => ( Real.exp ( -Real.exp ( -x ) / N ) * Real.exp ( -x ) / N ) / ( 1 - Real.exp ( -Real.exp ( -x ) / N ) );
            · refine' DifferentiableOn.div _ _ _ <;> norm_num [ DifferentiableOn.exp, DifferentiableOn.neg, DifferentiableOn.mul, DifferentiableOn.div, differentiableOn_id, differentiableOn_const ];
              · fun_prop (disch := norm_num);
              · exact DifferentiableOn.exp ( DifferentiableOn.div_const ( DifferentiableOn.neg ( DifferentiableOn.exp ( differentiableOn_id.neg ) ) ) _ );
              · exact fun x => sub_ne_zero_of_ne <| Ne.symm <| by norm_num ; positivity;
            · intro x hx; norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - Real.exp ( -Real.exp ( -x ) / N ) from sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| by { exact div_neg_of_neg_of_pos ( neg_lt_zero.mpr <| Real.exp_pos _ ) <| by positivity } ) ] ; ring;
              convert congr_arg Neg.neg ( HasDerivAt.deriv ( HasDerivAt.log ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.exp ( HasDerivAt.neg ( HasDerivAt.mul ( HasDerivAt.inv ( Real.hasDerivAt_exp _ ) <| ne_of_gt <| Real.exp_pos _ ) <| hasDerivAt_const _ _ ) ) ) ) <| show ( 1 - Real.exp ( - ( ( Real.exp x ) ⁻¹ * N⁻¹ ) ) ) ≠ 0 from sub_ne_zero.mpr <| Ne.symm <| by norm_num; positivity ) ) using 1 ; norm_num ; ring;
              norm_num [ sq, mul_assoc, Real.exp_ne_zero ];
          · -- Let's calculate the first derivative of $h_N(x)$.
            have h_deriv : ∀ x, deriv (fun x => -Real.log (1 - Real.exp (-Real.exp (-x) / N))) x = (Real.exp (-x) / N) * (Real.exp (-Real.exp (-x) / N)) / (1 - Real.exp (-Real.exp (-x) / N)) := by
              intro x; norm_num [ Real.exp_ne_zero, Real.exp_neg, Real.differentiableAt_exp, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < 1 - Real.exp ( -Real.exp ( -x ) / N ) from sub_pos.mpr <| by rw [ Real.exp_lt_one_iff ] ; exact div_neg_of_neg_of_pos ( neg_neg_of_pos <| Real.exp_pos _ ) <| by positivity ) ] ;
              norm_num [ Real.exp_ne_zero, Real.differentiableAt_exp, mul_comm, ne_of_gt ( show 0 < 1 - ( Real.exp ( N⁻¹ * ( Real.exp x ) ⁻¹ ) ) ⁻¹ from sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| by norm_num; positivity ) ] ; ring;
              norm_num [ sq, mul_assoc, Real.exp_ne_zero ];
            aesop;
            refine' ( HasDerivAt.deriv _ ) |> fun h => h.symm ▸ _;
            convert HasDerivAt.div ( HasDerivAt.mul ( HasDerivAt.div_const ( HasDerivAt.exp ( hasDerivAt_neg x ) ) _ ) ( HasDerivAt.exp ( HasDerivAt.div_const ( HasDerivAt.neg ( HasDerivAt.exp ( hasDerivAt_neg x ) ) ) _ ) ) ) ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.exp ( HasDerivAt.div_const ( HasDerivAt.neg ( HasDerivAt.exp ( hasDerivAt_neg x ) ) ) _ ) ) ) _ using 1;
            · exact ne_of_gt ( sub_pos_of_lt ( Real.exp_lt_one_iff.mpr ( by exact div_neg_of_neg_of_pos ( neg_neg_of_pos ( Real.exp_pos _ ) ) ( by positivity ) ) ) );
            · rw [ le_div_iff₀ ] <;> norm_num;
              · ring_nf;
                nlinarith only [ show 0 ≤ Real.exp ( -x ) * N⁻¹ * Real.exp ( - ( Real.exp ( -x ) * N⁻¹ ) ) by positivity, show 0 ≤ Real.exp ( -x ) ^ 2 * N⁻¹ ^ 2 * Real.exp ( - ( Real.exp ( -x ) * N⁻¹ ) ) by positivity, Real.exp_pos ( -x ), Real.exp_pos ( - ( Real.exp ( -x ) * N⁻¹ ) ), Real.add_one_le_exp ( - ( Real.exp ( -x ) * N⁻¹ ) ), Real.add_one_le_exp ( -x ) ];
              · exact pow_pos ( sub_pos_of_lt ( by rw [ Real.exp_lt_one_iff ] ; exact div_neg_of_neg_of_pos ( neg_neg_of_pos ( Real.exp_pos _ ) ) ( by positivity ) ) ) _;
        aesop;
        · exact convex_univ;
        · have := h_convex.2 ( Set.mem_univ x ) ( Set.mem_univ y ) a_1 a_2 a_3 ; aesop;
          rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt <| sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| by exact div_neg_of_neg_of_pos ( neg_lt_zero.mpr <| Real.exp_pos _ ) <| by positivity ), Real.log_mul ( by positivity ) ( by exact ne_of_gt <| sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| by exact div_neg_of_neg_of_pos ( neg_lt_zero.mpr <| Real.exp_pos _ ) <| by positivity ) ] at * ; aesop;
          rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt <| sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| by exact div_neg_of_neg_of_pos ( neg_lt_zero.mpr <| Real.exp_pos _ ) <| by positivity ) ] ; nlinarith [ Real.log_le_sub_one_of_pos <| show 0 < N by positivity ] ;
      · aesop;
        · rw [ lt_neg, Real.log_lt_iff_lt_exp ];
          · nlinarith [ Real.exp_pos ( -Real.exp ( -x ) / N ), Real.exp_neg ( -Real.exp ( -x ) / N ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( -Real.exp ( -x ) / N ) ) ), Real.add_one_lt_exp ( show -Real.exp ( -x ) / N ≠ 0 by exact div_ne_zero ( neg_ne_zero.mpr ( ne_of_gt ( Real.exp_pos _ ) ) ) ( by positivity ) ), Real.exp_pos ( -x ), Real.exp_neg x, mul_div_cancel₀ ( -Real.exp ( -x ) ) ( by positivity : ( N : ℝ ) ≠ 0 ) ];
          · exact mul_pos ( by positivity ) ( sub_pos_of_lt ( Real.exp_lt_one_iff.mpr ( by exact div_neg_of_neg_of_pos ( neg_lt_zero.mpr ( Real.exp_pos _ ) ) ( by positivity ) ) ) );
        · rw [ neg_le ];
          rw [ ← Real.log_exp ( - ( Real.exp ( -x ) / N + x ) ) ];
          gcongr;
          ring_nf;
          rw [ sub_eq_add_neg, Real.exp_add ];
          nlinarith [ inv_pos.mpr ( zero_lt_one.trans_le hN ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans_le hN ) ), Real.exp_pos ( -x ), Real.exp_pos ( - ( Real.exp ( -x ) * N⁻¹ ) ), Real.exp_neg ( Real.exp ( -x ) * N⁻¹ ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( Real.exp ( -x ) * N⁻¹ ) ) ), Real.add_one_le_exp ( -x ), Real.add_one_le_exp ( - ( Real.exp ( -x ) * N⁻¹ ) ), Real.add_one_le_exp ( Real.exp ( -x ) * N⁻¹ ), Real.exp_neg ( -x ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( -x ) ) ) ];
      · -- Let $y = \frac{e^{-x}}{N}$. Since $x > 0$ and $N \geq 1$, we have $0 < y \leq 1$.
        intro x hx_pos
        set y := Real.exp (-x) / N
        have hy_pos : 0 < y := by
          positivity
        have hy_le_one : y ≤ 1 := by
          exact div_le_one_of_le₀ ( le_trans ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr hx_pos.le ) ) hN ) ( by positivity );
        -- We want to prove $h_N(x) \geq \frac{y}{3}$, which is equivalent to $\frac{1 - e^{-y}}{y} \leq e^{-y/3}$.
        suffices h_ineq : (1 - Real.exp (-y)) / y ≤ Real.exp (-y / 3) by
          -- Taking the natural logarithm of both sides of the inequality $\frac{1 - e^{-y}}{y} \leq e^{-y/3}$, we get $-\ln\left(\frac{1 - e^{-y}}{y}\right) \geq \frac{y}{3}$.
          have h_log_ineq : -Real.log ((1 - Real.exp (-y)) / y) ≥ y / 3 := by
            have := Real.log_le_log ( div_pos ( sub_pos.mpr <| Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hy_pos ) hy_pos ) h_ineq ; norm_num at * ; linarith;
          rw [ Real.log_div ] at h_log_ineq <;> aesop;
          · rw [ Real.log_mul ] at * <;> aesop;
            · rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_exp ] at h_log_ineq ; ring_nf at * ; linarith;
            · exact absurd a <| ne_of_gt <| sub_pos_of_lt <| Real.exp_lt_one_iff.mpr <| by ring_nf; norm_num; positivity;
          · linarith;
        -- Consider $g(t) = 1 - t + \frac{t^2}{2} - \frac{t^3}{6} - e^{-t}$ for $t \geq 0$. Then $g'''(t) = -1 + e^{-t} \leq 0$, so $g(t) \leq 0$ for all $t \geq 0$.
        have h_g : ∀ t : ℝ, 0 ≤ t → 1 - t + t^2 / 2 - t^3 / 6 ≤ Real.exp (-t) := by
          -- Let's choose any $t \geq 0$ and derive the inequality.
          intro t ht
          have h_deriv : ∀ t : ℝ, 0 ≤ t → deriv (fun t => Real.exp t * (1 - t + t^2 / 2 - t^3 / 6)) t ≤ 0 := by
            intro t ht; norm_num [ Real.differentiableAt_exp, mul_comm, sub_add, add_assoc ] ; ring_nf; norm_num [ Real.exp_pos ] ;
            positivity;
          -- Since $g(t)$ is differentiable and its derivative is non-positive for $t \geq 0$, we can apply the Mean Value Theorem to $g(t)$ on the interval $[0, t]$.
          have h_mvt : ∀ t : ℝ, 0 < t → ∃ c ∈ Set.Ioo 0 t, deriv (fun t => Real.exp t * (1 - t + t^2 / 2 - t^3 / 6)) c = (Real.exp t * (1 - t + t^2 / 2 - t^3 / 6) - Real.exp 0 * (1 - 0 + 0^2 / 2 - 0^3 / 6)) / (t - 0) := by
            intros t ht_pos;
            have := exists_deriv_eq_slope ( f := fun t => Real.exp t * ( 1 - t + t ^ 2 / 2 - t ^ 3 / 6 ) ) ht_pos;
            exact this ( Continuous.continuousOn <| by exact Continuous.mul ( Real.continuous_exp ) <| by exact Continuous.sub ( Continuous.add ( continuous_const.sub continuous_id' ) <| continuous_pow 2 |> Continuous.div_const <| 2 ) <| continuous_pow 3 |> Continuous.div_const <| 6 ) ( Differentiable.differentiableOn <| by exact Differentiable.mul ( Real.differentiable_exp ) <| by exact Differentiable.sub ( Differentiable.add ( differentiable_const _ |> Differentiable.sub <| differentiable_id' ) <| differentiable_pow 2 |> Differentiable.div_const <| 2 ) <| differentiable_pow 3 |> Differentiable.div_const <| 6 );
          cases lt_or_eq_of_le ht <;> aesop;
          obtain ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ := h_mvt t h ; have := h_deriv c hc₁.le ; rw [ hc ] at this ; rw [ div_le_iff₀ <| by positivity ] at this ; nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ <| ne_of_gt <| Real.exp_pos t ];
        -- Hence $1 - e^{-t} \leq t - \frac{t^2}{2} + \frac{t^3}{6}$ so $\frac{1 - e^{-t}}{t} \leq 1 - \frac{t}{2} + \frac{t^2}{6} \leq 1 - \frac{t}{3}$ where the last inequality holds whenever $0 \leq t \leq 1$.
        have h_ineq : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → (1 - Real.exp (-t)) / t ≤ 1 - t / 3 := by
          intro t ht; rcases eq_or_lt_of_le ht.1 with ( rfl | ht₁ ) <;> [ norm_num; rw [ div_le_iff₀ ht₁ ] ] ; nlinarith [ h_g t ht.1 ] ;
        exact le_trans ( h_ineq y ⟨ hy_pos.le, hy_le_one ⟩ ) ( by linarith [ Real.add_one_le_exp ( -y / 3 ) ] )
