import Imports
import Coupling

/-!
# Gumbel Distribution and Transformation to Exponential

This file contains lemmas about the Gumbel distribution and its transformation
to the exponential distribution.
-/

open MeasureTheory ProbabilityTheory

/-
Calculation of the transformed CDF for positive y.
-/
lemma gumbel_exp_neg_cdf_calc (y : ℝ) (hy : 0 < y) :
    1 - gumbel_cdf (-Real.log y) = 1 - Real.exp (-y) := by
      unfold gumbel_cdf; norm_num [ Real.exp_neg, Real.exp_log hy ] ;

/-
The Gumbel CDF is continuous.
-/
lemma gumbel_cdf_continuous : Continuous gumbel_cdf := by
  exact Real.continuous_exp.comp <| Continuous.neg <| Real.continuous_exp.comp <| Continuous.neg continuous_id

/-
Set difference characterization of the interval (a, b].
-/
lemma set_Ioc_eq_diff {Ω : Type*} (Y : Ω → ℝ) (a b : ℝ) :
    {ω | a < Y ω ∧ Y ω ≤ b} = {ω | Y ω ≤ b} \ {ω | Y ω ≤ a} := by
      ext ω; aesop

/-
The CDF function F is monotone non-decreasing.
-/
lemma cdf_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (F : ℝ → ℝ)
    (h_cdf : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (F x))
    (hF_nonneg : ∀ x, 0 ≤ F x) :
    Monotone F := by
      -- By definition of F, we know that μ {ω | Y ω ≤ x} = ENNReal.ofReal (F x) and μ {ω | Y ω ≤ y} = ENNReal.ofReal (F y).
      have h_monotone : ∀ x y, x ≤ y → μ {ω | Y ω ≤ x} ≤ μ {ω | Y ω ≤ y} := by
        exact fun x y hxy => MeasureTheory.measure_mono fun ω hω => le_trans hω.out hxy;
      aesop

/-
The measure of an interval (a, b] is F(b) - F(a), assuming Y is measurable.
-/
lemma measure_Ioc_eq_cdf_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (F : ℝ → ℝ)
    (h_meas : Measurable Y)
    (h_cdf : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (F x))
    (hF_nonneg : ∀ x, 0 ≤ F x)
    (a b : ℝ) (hab : a < b) :
    μ {ω | a < Y ω ∧ Y ω ≤ b} = ENNReal.ofReal (F b - F a) := by
      rw [ show { ω | a < Y ω ∧ Y ω ≤ b } = { ω | Y ω ≤ b } \ { ω | Y ω ≤ a } by ext; aesop, MeasureTheory.measure_diff ] <;> norm_num [ h_cdf ];
      · rw [ ENNReal.ofReal_sub ] ; aesop;
      · exact fun ω hω => le_trans hω hab.le;
      · exact measurableSet_le h_meas measurable_const |> MeasurableSet.nullMeasurableSet

/-
The measure of (a, b] is the difference of the measures of (-inf, b] and (-inf, a].
-/
lemma measure_Ioc_eq_measure_le_sub_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (h_meas : Measurable Y)
    (a b : ℝ) (hab : a < b)
    (h_finite : μ {ω | Y ω ≤ a} ≠ ⊤) :
    μ {ω | a < Y ω ∧ Y ω ≤ b} = μ {ω | Y ω ≤ b} - μ {ω | Y ω ≤ a} := by
      rw [ ← MeasureTheory.measure_diff ];
      · exact congr_arg _ ( by ext; aesop );
      · exact fun x hx => le_trans hx.out hab.le;
      · exact h_meas.nullMeasurable measurableSet_Iic;
      · assumption

/-
If a random variable has a continuous CDF at y, the probability it equals y is 0.
-/
lemma measure_singleton_eq_zero_of_continuous_cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (F : ℝ → ℝ)
    (h_meas : Measurable Y)
    (y : ℝ)
    (h_cdf : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (F x))
    (hF_nonneg : ∀ x, 0 ≤ F x)
    (h_cont : ContinuousAt F y) :
    μ {ω | Y ω = y} = 0 := by
      -- By the squeeze theorem, since $\mu(y - 1/(n+1) < Y \le y)$ tends to $0$ as $n$ tends to infinity, we have $\mu(Y = y) \le 0$.
      have h_squeeze : Filter.Tendsto (fun n : ℕ => μ {ω | y - 1 / (n + 1) < Y ω ∧ Y ω ≤ y}) Filter.atTop (nhds 0) := by
        -- By the properties of the CDF, we have $\mu(y - 1/(n+1) < Y \le y) = ENNReal.ofReal (F(y) - F(y - 1/(n+1)))$.
        have h_cdf_interval : ∀ n : ℕ, μ {ω | y - 1 / (n + 1) < Y ω ∧ Y ω ≤ y} = ENNReal.ofReal (F y - F (y - 1 / (n + 1))) := by
          intro n;
          convert measure_Ioc_eq_cdf_sub μ Y F h_meas h_cdf hF_nonneg ( y - 1 / ( n + 1 ) ) y ( sub_lt_self _ ( by positivity ) ) using 1;
        aesop;
        simpa using ENNReal.tendsto_ofReal ( Filter.Tendsto.const_sub ( F y ) ( h_cont.tendsto.comp ( show Filter.Tendsto ( fun n : ℕ => y - ( n + 1 : ℝ ) ⁻¹ ) Filter.atTop ( nhds y ) by exact le_trans ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) ( by simp +decide ) ) ) );
      aesop;
      exact le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_squeeze fun n => by exact MeasureTheory.measure_mono <| fun ω hω => ⟨ by linarith [ hω.symm, inv_pos.mpr ( by linarith : 0 < ( n : ℝ ) + 1 ) ], by linarith [ hω.symm, inv_pos.mpr ( by linarith : 0 < ( n : ℝ ) + 1 ) ] ⟩ ) bot_le

/-
The difference F(y) - F(y - 1/(n+1)) tends to 0 if F is continuous at y.
-/
lemma cdf_diff_tendsto_zero (F : ℝ → ℝ) (y : ℝ) (h_cont : ContinuousAt F y) :
    Tendsto (fun n : ℕ => F y - F (y - 1 / (n + 1))) atTop (nhds 0) := by
      simpa using h_cont.tendsto.comp ( show Filter.Tendsto ( fun n : ℕ => y - ( n + 1 : ℝ ) ⁻¹ ) Filter.atTop ( nhds y ) by simpa using tendsto_const_nhds.sub ( tendsto_one_div_add_atTop_nhds_zero_nat ) ) |> fun h => h.const_sub ( F y )

/-
The measure of a singleton for a Gumbel variable is 0.
-/
lemma gumbel_measure_singleton_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (h_meas : Measurable Y)
    (hY : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (gumbel_cdf x)) (y : ℝ) :
    μ {ω | Y ω = y} = 0 := by
      -- Apply the lemma that states if a random variable has a continuous CDF at y, then the probability it equals y is 0.
      apply measure_singleton_eq_zero_of_continuous_cdf μ Y (fun x => gumbel_cdf x) h_meas y hY (fun x => by
        exact Real.exp_nonneg _) (by
      exact gumbel_cdf_continuous.continuousAt)

/-
The probability that a Gumbel variable is at least y is 1 - F(y).
-/
lemma gumbel_prob_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (h_meas : Measurable Y)
    (hY : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (gumbel_cdf x)) (y : ℝ) :
    μ {ω | Y ω ≥ y} = ENNReal.ofReal (1 - gumbel_cdf y) := by
      -- Since $Y$ is measurable, the set ${ω | y ≤ Y ω}$ is the complement of ${ω | Y ω ≤ y}$.
      have h_compl : μ {ω | y ≤ Y ω} = μ Set.univ - μ {ω | Y ω ≤ y} := by
        rw [ ← MeasureTheory.measure_diff ] <;> norm_num;
        · rw [ ← MeasureTheory.measure_congr ];
          rw [ MeasureTheory.ae_eq_set ] ; aesop;
          · exact MeasureTheory.measure_mono_null ( fun ω => by aesop ; linarith ) ( MeasureTheory.measure_empty );
          · rw [ show { ω | y ≤ Y ω } \ ( Set.univ \ { ω | Y ω ≤ y } ) = { ω | y ≤ Y ω ∧ y ≤ Y ω } ∩ { ω | Y ω ≤ y } by ext; aesop ] ; exact MeasureTheory.measure_mono_null ( fun x => by aesop ; linarith ) ( gumbel_measure_singleton_zero μ Y h_meas hY y );
        · exact h_meas.nullMeasurable measurableSet_Iic;
      rw [ ENNReal.ofReal_sub ] <;> aesop;
      exact Real.exp_nonneg _

/-
Transformation of Gumbel CDF to Exponential CDF.
-/
lemma gumbel_to_exp_cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (h_meas : Measurable Y)
    (hY : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (gumbel_cdf x)) :
    ∀ x, μ {ω | Real.exp (-Y ω) ≤ x} = ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-x) else 0) := by
      aesop;
      · by_cases hx : x = 0;
        · simp +decide [ hx, Real.exp_ne_zero ];
          exact MeasureTheory.measure_mono_null ( fun ω hω => by linarith [ Real.exp_pos ( -Y ω ), hω.out ] ) ( MeasureTheory.measure_empty );
        · convert gumbel_prob_ge μ Y h_meas hY ( -Real.log x ) using 1;
          · congr with ω ; aesop;
            · linarith [ Real.log_exp ( -Y ω ), Real.log_le_log ( by positivity ) a ];
            · rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ] ; linarith;
          · unfold gumbel_cdf; norm_num [ Real.exp_neg, Real.exp_log ( lt_of_le_of_ne h ( Ne.symm hx ) ) ] ;
      · exact MeasureTheory.measure_mono_null ( fun ω hω => by linarith [ hω.out, Real.exp_pos ( -Y ω ) ] ) ( MeasureTheory.measure_empty )

/-
For positive x, the CDF of exp(-Y) matches the exponential distribution.
-/
lemma gumbel_to_exp_cdf_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (h_meas : Measurable Y)
    (hY : ∀ x, μ {ω | Y ω ≤ x} = ENNReal.ofReal (gumbel_cdf x))
    (x : ℝ) (hx : 0 < x) :
    μ {ω | Real.exp (-Y ω) ≤ x} = ENNReal.ofReal (1 - Real.exp (-x)) := by
      convert gumbel_to_exp_cdf μ Y h_meas hY x using 1;
      rw [ if_pos hx.le ]

/-
For non-positive x, the probability that exp(-Y) <= x is 0.
-/
lemma gumbel_to_exp_cdf_nonpos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (x : ℝ) (hx : x ≤ 0) :
    μ {ω | Real.exp (-Y ω) ≤ x} = 0 := by
      exact MeasureTheory.measure_mono_null ( fun ω hω => by linarith [ Real.exp_pos ( -Y ω ), hω.out ] ) ( MeasureTheory.measure_empty )


/-
If Y is a Gumbel grid (and measurable), then exp(-Y) is an exponential grid.
-/
lemma exp_neg_Y_is_exp_grid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Edge → Ω → ℝ) (hY : IsGumbelGrid μ Y) (h_meas : ∀ e, Measurable (Y e)) :
    iIndepFun (fun e ω => Real.exp (-Y e ω)) μ ∧
    ∀ e x, μ {ω | Real.exp (-Y e ω) ≤ x} = ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-x) else 0) := by
      constructor;
      · exact hY.1.comp ( fun e => Real.exp ∘ Neg.neg ) fun e => Real.continuous_exp.measurable.comp ( measurable_id'.neg );
      · intro e x;
        convert gumbel_to_exp_cdf μ ( Y e ) ( h_meas e ) ( hY.2 e ) x using 1
