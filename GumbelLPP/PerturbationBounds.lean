import GumbelLPP.Imports

/-!
# Perturbation Bounds for LPP Models

This file contains Lemma 2, which provides bounds for perturbation analysis
of Last Passage Percolation models.
-/

/-
Lemma 2: Perturbation bounds for LPP models.
-/
theorem lemma_2 {Pi : Type*} [Fintype Pi] [Nonempty Pi]
    (S_A S_B : Pi → ℝ) (pi_star : Pi)
    (h_pi_star : ∀ p, S_A p ≤ S_A pi_star) :
    let M_A := S_A pi_star
    let M_AB := (Finset.univ.image (fun p => S_A p + S_B p)).max' (Finset.univ_nonempty.image _)
    let m_B := (Finset.univ.image S_B).min' (Finset.univ_nonempty.image _)
    let M_B := (Finset.univ.image S_B).max' (Finset.univ_nonempty.image _)
    m_B ≤ S_B pi_star ∧
    S_B pi_star ≤ M_AB - M_A ∧
    M_AB - M_A ≤ M_B := by
      aesop;
      · exact Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) );
      · exact le_tsub_of_add_le_left ( by simpa [ add_comm ] using Finset.le_max' _ _ ( Finset.mem_image_of_mem ( fun p => S_A p + S_B p ) ( Finset.mem_univ pi_star ) ) );
      · linarith [ h_pi_star a, Finset.le_max' ( Finset.image S_B Finset.univ ) ( S_B a ) ( Finset.mem_image_of_mem _ ( Finset.mem_univ a ) ) ]
