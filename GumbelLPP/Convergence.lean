import GumbelLPP.Imports
import GumbelLPP.Coupling

/-!
# Convergence Properties and Probability Definitions

This file defines convergence properties for LPP models, including convergence
in probability and time constant properties.
-/

open Filter Topology MeasureTheory ProbabilityTheory

/-
Definitions of the properties representing known results from the paper.
-/
def ExactGumbelConvergenceProperty : Prop :=
  ∀ (r : ℝ),
  ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, Edge → Ω n → ℝ),
  (∀ n, IsGumbelGrid (μ n) (Y n)) →
  Tendsto (fun n => ((μ n) {ω | (T_Gumbel n n (Y n) ω - C_g * n) / (sigma_g * (n : ℝ) ^ (1/3 : ℝ)) ≤ r}).toReal) atTop (𝓝 (F_GUE r))

def TimeConstantGumbelProperty : Prop :=
  ∃ D_ell > 0, ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, Edge → Ω n → ℝ),
  (∀ n, IsGumbelGrid (μ n) (Y n)) →
  ∀ ε > 0, Tendsto (fun n => ((μ n) {ω | |T_Gumbel n n (Y n) ω / n - D_ell| > ε}).toReal) atTop (𝓝 0)

def TimeConstantExpProperty : Prop :=
  ∃ D_L > 0, ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) (E : ∀ n, Edge → Ω n → ℝ),
  (∀ n, iIndepFun (E n) (μ n) ∧ ∀ e x, (μ n) {ω | E n e ω ≤ x} = ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-x) else 0)) →
  ∀ ε > 0, Tendsto (fun n => ((μ n) {ω | |L_Exp n n (E n) ω / n - D_L| > ε}).toReal) atTop (𝓝 0)

/-
Definition of convergence in probability to 0.
-/
/-- Convergence in probability to 0. -/
def ConvergesInProbZero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => ((μ n) {ω | |Y n ω| > ε}).toReal) atTop (𝓝 0)

/-
Definition of convergence in probability to a constant.
-/
/-- Convergence in probability to a constant. -/
def ConvergesInProbConst {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => ((μ n) {ω | |Y n ω - c| > ε}).toReal) atTop (𝓝 0)

/-
If $|y| > |c| + 1$, then $|y - c| > 1$.
-/
lemma abs_gt_of_abs_sub_gt (y c : ℝ) : |y| > |c| + 1 → |y - c| > 1 := by
  cases abs_cases ( y - c ) <;> cases abs_cases y <;> cases abs_cases c <;> intros <;> linarith

/-
If $Y_n \to c$ in probability, then $P(|Y_n| > |c| + 1) \to 0$.
-/
lemma converges_in_prob_bounded {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (Y : ∀ n, Ω n → ℝ) (c : ℝ)
    (h : ConvergesInProbConst μ Y c) :
    Tendsto (fun n => ((μ n) {ω | |Y n ω| > |c| + 1}).toReal) atTop (𝓝 0) := by
      have h_bound : ∀ n, ((μ n) {ω | |Y n ω| > |c| + 1}).toReal ≤ ((μ n) {ω | |Y n ω - c| > 1}).toReal := by
        intro n; apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ] ; aesop;
        exact fun ω hω => by norm_num at *; cases abs_cases ( Y n ω ) <;> cases abs_cases c <;> cases abs_cases ( Y n ω - c ) <;> linarith;
      exact squeeze_zero ( fun n => ENNReal.toReal_nonneg ) h_bound ( by simpa using h 1 zero_lt_one )

/-
Product of a sequence converging in probability to a constant and a sequence converging to 0 converges in probability to 0.
-/
lemma converges_in_prob_mul_zero {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (Y : ∀ n, Ω n → ℝ) (c : ℝ) (a : ℕ → ℝ)
    (h_Y : ConvergesInProbConst μ Y c)
    (h_a : Tendsto a atTop (𝓝 0)) :
    ConvergesInProbZero μ (fun n ω => a n * Y n ω) := by
      intro ε hε;
      -- Fix $\epsilon > 0$. Since $a_n \to 0$, there exists $N$ such that for all $n \ge N$, $|a_n| < \frac{\epsilon}{|c| + 1}$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, |a n| < ε / (|c| + 1) := by
        simpa using h_a.eventually ( Metric.ball_mem_nhds _ <| by positivity );
      -- For such $n$, if $|Y_n| \le |c| + 1$, then $|a_n Y_n| < \frac{\epsilon}{|c| + 1} (|c| + 1) = \epsilon$.
      have h_bound : ∀ n ≥ N, {ω | ε < |a n * Y n ω|} ⊆ {ω | |Y n ω| > |c| + 1} := by
        intro n hn ω hω; specialize hN n hn; rw [ lt_div_iff₀ ( by positivity ) ] at hN; contrapose! hω; aesop;
        exact le_trans ( mul_le_mul_of_nonneg_left hω ( abs_nonneg _ ) ) hN.le;
      -- Thus, for $n \ge N$, $\mu(\{|a_n Y_n| > \epsilon\}) \le \mu(\{|Y_n| > |c| + 1\})$.
      have h_measure_bound : ∀ n ≥ N, ((μ n) {ω | ε < |a n * Y n ω|}).toReal ≤ ((μ n) {ω | |Y n ω| > |c| + 1}).toReal := by
        exact fun n hn => ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( h_bound n hn ) );
      exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ N, fun n hn => by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact h_measure_bound n hn ⟩ ) ( converges_in_prob_bounded μ Y c h_Y )

/-
If $0 \le X \le Z$, then $P(|X| > \epsilon) \le P(|Z| > \epsilon)$.
-/
lemma squeeze_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Z : Ω → ℝ) (ε : ℝ)
    (h_nonneg : ∀ ω, 0 ≤ X ω)
    (h_le : ∀ ω, X ω ≤ Z ω) :
    μ {ω | |X ω| > ε} ≤ μ {ω | |Z ω| > ε} := by
      apply_rules [ MeasureTheory.measure_mono ];
      aesop;
      cases abs_cases ( X a ) <;> cases abs_cases ( Z a ) <;> linarith [ h_nonneg a, h_le a ]

/-
The deterministic factor in the error term converges to 0.
-/
lemma deterministic_factor_limit (α : ℝ) (h_alpha : α > 2/3) :
    Tendsto (fun n => (n : ℝ) / (Nat.floor ((n : ℝ) ^ α) * (n : ℝ) ^ (1/3 : ℝ))) atTop (𝓝 0) := by
      -- We can factor out $n^{1/3}$ from the denominator and use the fact that $⌊n^\alpha⌋₊$ is approximately $n^\alpha$ for large $n$.
      have h_factor : Tendsto (fun n => (n : ℝ) ^ (1 - α - 1 / 3 : ℝ)) Filter.atTop (nhds 0) := by
        simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( 1 - α - 1 / 3 ) );
      -- Using the fact that $⌊n^\alpha⌋₊$ is approximately $n^\alpha$ for large $n$, we can bound the expression.
      have h_bound : ∀ᶠ n in Filter.atTop, (n : ℝ) / (⌊n ^ α⌋₊ * n ^ (1 / 3 : ℝ)) ≤ 2 * (n : ℝ) ^ (1 - α - 1 / 3 : ℝ) := by
        -- Using the fact that $⌊n^\alpha⌋₊$ is approximately $n^\alpha$ for large $n$, we can bound the expression as follows:
        have h_bound : ∀ᶠ n in Filter.atTop, (n : ℝ) / (⌊n ^ α⌋₊ * n ^ (1 / 3 : ℝ)) ≤ (n : ℝ) / ((n ^ α / 2) * n ^ (1 / 3 : ℝ)) := by
          filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( 2 ^ ( 1 / α ) ) ] with n hn hn';
          gcongr;
          linarith [ Nat.lt_floor_add_one ( n ^ α ), show ( n : ℝ ) ^ α ≥ 2 by exact le_trans ( by exact le_of_eq ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ) ) ( Real.rpow_le_rpow ( by positivity ) hn'.le ( by positivity ) ) ];
        filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' ; convert hn using 1 ; ring;
        rw [ show ( 2 / 3 - α : ℝ ) = 1 - α - 1 / 3 by ring, Real.rpow_sub hn', Real.rpow_sub hn' ] ; norm_num ; ring;
      refine' squeeze_zero_norm' _ _;
      exacts [ fun n => 2 * n ^ ( 1 - α - 1 / 3 ), by filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact hn, by simpa using h_factor.const_mul 2 ]
