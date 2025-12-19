import GumbelLPP.Imports
import GumbelLPP.Convergence

/-!
# Slutsky's Theorem for CDFs

This file contains Slutsky's theorem and related inequalities for cumulative
distribution functions.
-/

open Filter Topology MeasureTheory ProbabilityTheory

/-
Upper bound inequality for Slutsky's theorem.
-/
theorem slutsky_upper_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (r ε : ℝ) :
    μ {ω | X ω + Y ω ≤ r} ≤ μ {ω | X ω ≤ r + ε} + μ {ω | |Y ω| > ε} := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      intro ω hω; contrapose! hω; aesop; cases abs_cases ( Y ω ) <;> linarith;

/-
Lower bound inequality for Slutsky's theorem.
-/
theorem slutsky_lower_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (r ε : ℝ) :
    μ {ω | X ω ≤ r - ε} ≤ μ {ω | X ω + Y ω ≤ r} + μ {ω | |Y ω| > ε} := by
      refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
      refine' MeasureTheory.measure_mono fun ω hω => _;
      norm_num +zetaDelta at *;
      contrapose! hω; cases abs_cases ( Y ω ) <;> linarith;

/-
If $a_n \le b_n + c_n$, $b_n \to B$, and $c_n \to 0$, then eventually $a_n \le B + \epsilon$.
-/
lemma limit_upper_bound_helper (a b c : ℕ → ℝ) (B : ℝ)
    (hb : Tendsto b atTop (𝓝 B))
    (hc : Tendsto c atTop (𝓝 0))
    (h_le : ∀ n, a n ≤ b n + c n) :
    ∀ ε > 0, ∀ᶠ n in atTop, a n ≤ B + ε := by
      intro ε hε; filter_upwards [ hb.eventually ( Metric.ball_mem_nhds B <| half_pos hε ), hc.eventually ( Metric.ball_mem_nhds _ <| half_pos hε ) ] with n hn hn' using by linarith [ h_le n, abs_lt.mp <| Metric.mem_ball.mp hn, abs_lt.mp <| Metric.mem_ball.mp hn' ] ;

/-
Upper bound direction for Slutsky's theorem.
-/
theorem slutsky_cdf_upper {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (F : ℝ → ℝ)
    (h_cont : Continuous F)
    (h_X : ∀ r, Tendsto (fun n => ((μ n) {ω | X n ω ≤ r}).toReal) atTop (𝓝 (F r)))
    (h_Y : ConvergesInProbZero μ Y)
    (r : ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ((μ n) {ω | X n ω + Y n ω ≤ r}).toReal ≤ F r + ε := by
      -- For any $\epsilon > 0$, choose $\delta > 0$ such that $F(r + \delta) < F(r) + \epsilon / 2$.
      intro ε hε_pos
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, F (r + δ) < F r + ε / 2 := by
        have := Metric.continuous_iff.mp h_cont r ( ε / 2 ) ( half_pos hε_pos ) ; aesop;
        exact ⟨ w / 2, half_pos left, by linarith [ abs_lt.mp ( right ( r + w / 2 ) ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ] ⟩;
      -- By `slutsky_upper_bound` with $\delta$, we have $\mu(\dots) \le \mu(\dots) + \mu(\dots)$ in ENNReal.
      have h_upper_bound : ∀ n, ((μ n) {ω | X n ω + Y n ω ≤ r}).toReal ≤ ((μ n) {ω | X n ω ≤ r + δ}).toReal + ((μ n) {ω | |Y n ω| > δ}).toReal := by
        intro n;
        convert ENNReal.toReal_mono _ ( slutsky_upper_bound ( μ n ) ( X n ) ( Y n ) r δ ) using 1;
        · rw [ ENNReal.toReal_add ] <;> norm_num;
        · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ MeasureTheory.measure_lt_top _ _, MeasureTheory.measure_lt_top _ _ ⟩ );
      have := h_X ( r + δ );
      filter_upwards [ this.eventually ( gt_mem_nhds <| show F ( r + δ ) < F r + ε / 2 by linarith ), h_Y δ hδ_pos |> fun h => h.eventually ( gt_mem_nhds <| show ( 0 : ℝ ) < ε / 2 by linarith ) ] with n hn hn' using by linarith [ h_upper_bound n ] ;

/-
Real-valued version of Slutsky upper bound inequality.
-/
theorem slutsky_upper_bound_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℝ) (r ε : ℝ) :
    (μ {ω | X ω + Y ω ≤ r}).toReal ≤ (μ {ω | X ω ≤ r + ε}).toReal + (μ {ω | |Y ω| > ε}).toReal := by
      have := @slutsky_upper_bound Ω _ μ X Y r ε ; aesop;
      convert ENNReal.toReal_mono _ this using 1 <;> norm_num [ ENNReal.toReal_add ]

/-
If $a_n \ge b_n - c_n$, $b_n \to B$, and $c_n \to 0$, then eventually $a_n \ge B - \epsilon$.
-/
lemma limit_lower_bound_helper (a b c : ℕ → ℝ) (B : ℝ)
    (hb : Tendsto b atTop (𝓝 B))
    (hc : Tendsto c atTop (𝓝 0))
    (h_ge : ∀ n, a n ≥ b n - c n) :
    ∀ ε > 0, ∀ᶠ n in atTop, a n ≥ B - ε := by
      intro ε hε;
      filter_upwards [ hb.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) ), hc.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) ) ] with n hn hb using by linarith [ abs_lt.mp hn, abs_lt.mp hb, h_ge n ] ;

/-
Lower bound direction for Slutsky's theorem.
-/
theorem slutsky_cdf_lower {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (F : ℝ → ℝ)
    (h_cont : Continuous F)
    (h_X : ∀ r, Tendsto (fun n => ((μ n) {ω | X n ω ≤ r}).toReal) atTop (𝓝 (F r)))
    (h_Y : ConvergesInProbZero μ Y)
    (r : ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ((μ n) {ω | X n ω + Y n ω ≤ r}).toReal ≥ F r - ε := by
      aesop;
      -- Fix $\delta > 0$ such that $F(r - \delta) > F(r) - \frac{\epsilon}{2}$.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, F r - ε / 2 < F (r - δ) := by
        have := Metric.continuous_iff.1 h_cont ( r ) ( ε / 2 ) ( half_pos a ) ; aesop;
        exact ⟨ w / 2, half_pos left, by linarith [ abs_lt.mp ( right ( r - w / 2 ) ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) ] ⟩;
      -- By `slutsky_lower_bound` with $\delta$, we have $b_n \le a_n + c_n$, so $a_n \ge b_n - c_n$.
      have h_lower_bound : ∀ n, (((μ n) {ω | (X n ω) ≤ r - δ}).toReal) ≤ (((μ n) {ω | (X n ω) + (Y n ω) ≤ r}).toReal) + (((μ n) {ω | |(Y n ω)| > δ}).toReal) := by
        have h_lower_bound : ∀ n, (μ n) {ω | (X n ω) ≤ r - δ} ≤ (μ n) {ω | (X n ω) + (Y n ω) ≤ r} + (μ n) {ω | |(Y n ω)| > δ} := by
          exact?;
        intro n; specialize h_lower_bound n; rw [ ← ENNReal.toReal_add ] ; aesop;
        · exact MeasureTheory.measure_ne_top _ _;
        · exact MeasureTheory.measure_ne_top _ _;
      -- We have $b_n \to F(r - \delta)$ (by `h_X`) and $c_n \to 0$ (by `h_Y`).
      have h_b_c : Filter.Tendsto (fun n => (((μ n) {ω | (X n ω) ≤ r - δ}).toReal)) Filter.atTop (𝓝 (F (r - δ))) ∧ Filter.Tendsto (fun n => (((μ n) {ω | |(Y n ω)| > δ}).toReal)) Filter.atTop (𝓝 0) := by
        exact ⟨ h_X _, by simpa using h_Y δ hδ_pos ⟩;
      rcases Metric.tendsto_atTop.mp h_b_c.1 ( ε / 4 ) ( by linarith ) with ⟨ N₁, hN₁ ⟩ ; rcases Metric.tendsto_atTop.mp h_b_c.2 ( ε / 4 ) ( by linarith ) with ⟨ N₂, hN₂ ⟩ ; exact ⟨ Max.max N₁ N₂, fun n hn => by linarith [ abs_lt.mp ( hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ), abs_lt.mp ( hN₂ n ( le_trans ( le_max_right _ _ ) hn ) ), h_lower_bound n ] ⟩

/-
Slutsky's theorem for CDFs.
-/
theorem slutsky_cdf {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (F : ℝ → ℝ)
    (h_cont : Continuous F)
    (h_X : ∀ r, Tendsto (fun n => ((μ n) {ω | X n ω ≤ r}).toReal) atTop (𝓝 (F r)))
    (h_Y : ConvergesInProbZero μ Y) :
    ∀ r, Tendsto (fun n => ((μ n) {ω | X n ω + Y n ω ≤ r}).toReal) atTop (𝓝 (F r)) := by
      intro r
      have h_upper : ∀ ε > 0, ∀ᶠ n in atTop, ((μ n) {ω | X n ω + Y n ω ≤ r}).toReal ≤ F r + ε := by
        exact?
      have h_lower : ∀ ε > 0, ∀ᶠ n in atTop, ((μ n) {ω | X n ω + Y n ω ≤ r}).toReal ≥ F r - ε := by
        exact?
      exact (by
      rw [ Metric.tendsto_nhds ];
      exact fun ε εpos => by filter_upwards [ h_upper ( ε / 2 ) ( half_pos εpos ), h_lower ( ε / 2 ) ( half_pos εpos ) ] with n hn₁ hn₂ using abs_lt.mpr ⟨ by linarith, by linarith ⟩ ;)
