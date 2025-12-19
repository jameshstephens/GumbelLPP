import GumbelLPP.Imports
import GumbelLPP.GumbelFunction
import GumbelLPP.GridPaths

/-!
# Coupling Between Gumbel and Approximate Gumbel Distributions

This file defines the coupling between exact and approximate Gumbel distributions,
and proves upper and lower bounds for the difference in Last Passage Percolation values.
-/

open MeasureTheory ProbabilityTheory

/-
CDF of the N-approximate Gumbel distribution.
-/
noncomputable def f_approx_gumbel (N : ℝ) (x : ℝ) : ℝ :=
  if x > -Real.log N then (1 - Real.exp (-x) / N) ^ N else 0

/-
CDF of the Gumbel distribution.
-/
noncomputable def gumbel_cdf (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

/-
The coupling identity: g(y) = f_N(h_N(y) + y).
-/
theorem coupling_identity (N : ℝ) (hN : 1 ≤ N) (y : ℝ) :
    gumbel_cdf y = f_approx_gumbel N (h N y + y) := by
      unfold gumbel_cdf f_approx_gumbel h;
      rw [ Real.exp_neg, inv_eq_iff_eq_inv ] ; norm_num;
      rw [ if_pos ];
      · rw [ Real.exp_log ];
        · rw [ mul_div_cancel_left₀ _ ( by positivity ), sub_sub_cancel, ← Real.exp_mul ] ; ring;
          norm_num [ show N ≠ 0 by linarith ];
          rw [ ← Real.exp_neg, neg_neg ];
        · exact mul_pos ( by positivity ) ( sub_pos_of_lt ( Real.exp_lt_one_iff.mpr ( by ring_nf; norm_num; positivity ) ) );
      · exact Real.log_lt_log ( mul_pos ( by positivity ) ( sub_pos.mpr ( by rw [ Real.exp_lt_one_iff ] ; exact div_neg_of_neg_of_pos ( neg_lt_zero.mpr ( Real.exp_pos _ ) ) ( by positivity ) ) ) ) ( mul_lt_of_lt_one_right ( by positivity ) ( sub_lt_self _ ( by positivity ) ) )

/-
Definitions of T_Gumbel, T_Approx, and L_Exp.
-/
noncomputable def T_Gumbel (m n : ℕ) {Ω : Type*} (Y : Edge → Ω → ℝ) : Ω → ℝ :=
  fun ω => LPP_value m n (fun e => Y e ω)

noncomputable def T_Approx (m n : ℕ) (N : ℝ) {Ω : Type*} (Y : Edge → Ω → ℝ) : Ω → ℝ :=
  fun ω => LPP_value m n (fun e => h N (Y e ω) + Y e ω)

noncomputable def L_Exp (m n : ℕ) {Ω : Type*} (E : Edge → Ω → ℝ) : Ω → ℝ :=
  fun ω => LPP_value m n (fun e => E e ω)

/-
Constants C_g, sigma_g and the Tracy-Widom GUE distribution F_GUE.
-/
opaque C_g : ℝ
opaque sigma_g : ℝ
opaque F_GUE : ℝ → ℝ

/-
Checking the signature of iIndepFun.
-/
#check iIndepFun

/-
Definition of a grid of i.i.d. Gumbel random variables.
-/
def IsGumbelGrid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Edge → Ω → ℝ) : Prop :=
  iIndepFun Y μ ∧ ∀ e x, μ {ω | Y e ω ≤ x} = ENNReal.ofReal (gumbel_cdf x)

/-
Checking for MeasurableSpace instance on Real and borel definition.
-/
#synth MeasurableSpace ℝ
#check borel

/-
The scaled and centered LPP random variable.
-/
noncomputable def scaled_centered_LPP (n : ℕ) (N : ℝ) {Ω : Type*} (Y : Edge → Ω → ℝ) : Ω → ℝ :=
  fun ω => (T_Approx n n N Y ω - C_g * n) / (sigma_g * (n : ℝ) ^ (1/3 : ℝ))

/-
Definition of a grid of i.i.d. N-approximate Gumbel random variables.
-/
def IsApproxGumbelGrid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℝ) (Y : Edge → Ω → ℝ) : Prop :=
  iIndepFun Y μ ∧ ∀ e x, μ {ω | Y e ω ≤ x} = ENNReal.ofReal (f_approx_gumbel N x)

/-
The sequence of probabilities in the main theorem.
-/
noncomputable def prob_seq (α : ℝ) (r : ℝ)
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, Edge → Ω n → ℝ) (n : ℕ) : ℝ :=
  ((μ n) {ω | scaled_centered_LPP n (Nat.floor ((n : ℝ) ^ α)) (Y n) ω ≤ r}).toReal

/-
Upper bound on the difference between approximate and exact Gumbel LPP.
-/
theorem coupling_upper_bound (n : ℕ) (N : ℝ) (hN : 1 ≤ N) {Ω : Type*} (Y : Edge → Ω → ℝ) (ω : Ω) :
    T_Approx n n N Y ω - T_Gumbel n n Y ω ≤ (1 / N) * L_Exp n n (fun e ω => Real.exp (- (Y e ω))) ω := by
      norm_num [ T_Approx, T_Gumbel, L_Exp ];
      unfold LPP_value;
      rw [ Finset.max'_le_iff ];
      aesop;
      refine' add_le_add _ _;
      · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.le_max' _ _ <| Finset.mem_image_of_mem _ left ) <| by positivity );
        -- By Lemma 1, we know that $h_N(x) \leq e^{-x}/N$ for all $x$.
        have h_le : ∀ x : ℝ, h N x ≤ Real.exp (-x) / N := by
          exact fun x => lemma_1 N hN |>.2.1 x |>.2;
        simpa [ div_eq_inv_mul, List.sum_map_mul_left ] using List.sum_le_sum fun x hx => h_le ( Y x ω );
      · exact Finset.le_max' ( Finset.image ( fun p => ( List.map ( fun e => Y e ω ) p ).sum ) ( paths n n ) ) _ ( Finset.mem_image_of_mem _ left )

/-
Lower bound on the difference between approximate and exact Gumbel LPP using Jensen's inequality.
-/
theorem coupling_lower_bound (n : ℕ) (N : ℝ) (hN : 1 ≤ N) {Ω : Type*} (Y : Edge → Ω → ℝ) (ω : Ω) :
    2 * n * h N (T_Gumbel n n Y ω / (2 * n)) ≤ T_Approx n n N Y ω - T_Gumbel n n Y ω := by
      rcases eq_or_ne n 0 with ( rfl | hn ) <;> norm_num at *;
      · unfold T_Gumbel T_Approx;
        unfold LPP_value; aesop;
        refine' le_trans _ ( Finset.le_max' _ _ <| Finset.mem_image_of_mem _ a_1 ) ; aesop;
        -- Since $h_N(x)$ is non-negative for all $x$, the sum of $h_N(Y_i \omega)$ over any path is also non-negative.
        have h_nonneg : ∀ x : ℝ, 0 ≤ h N x := by
          exact fun x => by have := lemma_1 N hN; exact this.2.1 x |>.1.le;
        exact List.sum_nonneg ( by aesop );
      · -- Let's denote the geodesic (maximizing path) for $T_{Gumbel}$ as $\pi^*$.
        obtain ⟨pi_star, h_pi_star⟩ : ∃ pi_star : GridPath, IsValidPath (0, 0) (n, n) pi_star ∧ (pi_star.map (fun e => Y e ω)).sum = T_Gumbel n n Y ω := by
          have h_exists_pi_star : ∃ pi_star ∈ paths n n, (pi_star.map (fun e => Y e ω)).sum = T_Gumbel n n Y ω := by
            have := Finset.max'_mem ( Finset.image ( fun p : GridPath => ( p.map ( fun e => Y e ω ) ).sum ) ( paths n n ) ) ⟨ _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( paths_nonempty n n ) ) ⟩ ; aesop;
          unfold paths at h_exists_pi_star; aesop;
        -- By Jensen's inequality and convexity of $h_N$, we have $\frac{1}{2n} \sum_{e \in \pi^*} h_N(Y_e) \ge h_N(\frac{1}{2n} \sum_{e \in \pi^*} Y_e)$.
        have h_jensen : (pi_star.map (fun e => h N (Y e ω))).sum ≥ 2 * n * h N ((pi_star.map (fun e => Y e ω)).sum / (2 * n)) := by
          -- Since $\pi^*$ is a valid path from $(0,0)$ to $(n,n)$, it has length $2n$.
          have h_pi_star_length : (pi_star.length : ℝ) = 2 * n := by
            have h_pi_star_length : ∀ {p q : GridPoint} {l : GridPath}, IsValidPath p q l → (l.length : ℝ) = q.1 + q.2 - p.1 - p.2 := by
              intros p q l hl; induction hl <;> aesop;
              cases h_edge <;> aesop <;> linarith;
            exact h_pi_star_length h_pi_star.1 ▸ by push_cast; ring;
          have h_jensen : ∀ (f : ℝ → ℝ), ConvexOn ℝ (Set.univ : Set ℝ) f → ∀ (x : List ℝ), x.length = 2 * n → (List.map f x).sum ≥ 2 * n * f ((List.sum x) / (2 * n)) := by
            intros f hf x hx_length
            have h_jensen : (∑ i ∈ Finset.range (2 * n), f (x.get! i)) ≥ 2 * n * f ((∑ i ∈ Finset.range (2 * n), x.get! i) / (2 * n)) := by
              have h_jensen : (∑ i ∈ Finset.range (2 * n), (1 / (2 * n)) * f (x.get! i)) ≥ f ((∑ i ∈ Finset.range (2 * n), (1 / (2 * n)) * x.get! i)) := by
                apply ConvexOn.map_sum_le hf;
                · exact fun _ _ => by positivity;
                · simp +decide [ hn ];
                  ring_nf; norm_num [ hn ];
                · exact fun _ _ => Set.mem_univ _;
              simp_all +decide [ div_eq_inv_mul, ← Finset.mul_sum _ _ _ ];
              convert mul_le_mul_of_nonneg_left h_jensen ( show ( 0 : ℝ ) ≤ 2 * n by positivity ) using 1 ; ring_nf ; norm_num [ hn ];
            convert h_jensen using 1;
            · rw [ ← hx_length, Finset.sum_range ];
              simp +decide [ List.sum_eq_foldr, Finset.sum_range, List.get! ];
            · norm_num [ ← hx_length, Finset.sum_range, List.get! ];
          convert h_jensen ( fun x => h N x ) ( lemma_1 N hN |>.1 ) ( List.map ( fun e => Y e ω ) pi_star ) _ using 1;
          · rw [ List.map_map ];
            rfl;
          · simpa using mod_cast h_pi_star_length;
        -- Since $\pi^*$ is a valid path, we have $T_{Approx} \ge S_B(\pi^*) + T_{Gumbel}$.
        have h_approx_ge : T_Approx n n N Y ω ≥ (pi_star.map (fun e => h N (Y e ω) + Y e ω)).sum := by
          refine' Finset.le_max' _ _ _;
          unfold paths; aesop;
        simp_all +decide [ List.sum_map_add ];
        linarith

/-
The difference between the approximate and exact LPP is non-negative and bounded by the exponential LPP scaled by 1/N.
-/
lemma coupling_ineq_lift (n : ℕ) (N : ℝ) (hN : 1 ≤ N) {Ω : Type*} (Y : Edge → Ω → ℝ) (ω : Ω) :
    0 ≤ T_Approx n n N Y ω - T_Gumbel n n Y ω ∧
    T_Approx n n N Y ω - T_Gumbel n n Y ω ≤ (1 / N) * L_Exp n n (fun e ω => Real.exp (- (Y e ω))) ω := by
      refine' ⟨ _, _ ⟩;
      · refine' le_trans _ ( coupling_lower_bound n N hN Y ω );
        exact mul_nonneg ( by positivity ) ( lemma_1 N hN |>.2.1 _ |>.1.le );
      · exact?
