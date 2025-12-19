import Imports

/-!
# Grid Paths and Last Passage Percolation

This file defines grid points, edges, valid paths, and the Last Passage Percolation
value function on a grid.
-/

/-
Definitions of GridPoint, Edge, GridPath, and IsValidPath.
-/
/-- A point in the grid $\mathbb{N}^2$. -/
def GridPoint := ℕ × ℕ

/-- An edge in the grid. -/
def Edge := GridPoint × GridPoint

/-- An edge is up-right if it goes from $(x,y)$ to $(x+1,y)$ or $(x,y+1)$. -/
def is_up_right (e : Edge) : Prop :=
  (e.2.1 = e.1.1 + 1 ∧ e.2.2 = e.1.2) ∨ (e.2.1 = e.1.1 ∧ e.2.2 = e.1.2 + 1)

/-- A path is a list of edges. -/
def GridPath := List Edge

/-- A path is valid from start to end if it is a sequence of connected up-right edges. -/
inductive IsValidPath : GridPoint → GridPoint → GridPath → Prop
  | nil (p : GridPoint) : IsValidPath p p []
  | cons (p q r : GridPoint) (l : GridPath) (h_edge : is_up_right (p, q)) (h_path : IsValidPath q r l) :
    IsValidPath p r ((p, q) :: l)

/-
The set of all valid paths from $(0,0)$ to $(m,n)$.
-/
noncomputable def paths (m n : ℕ) : Finset GridPath :=
  let s := { l : GridPath | IsValidPath (0,0) (m,n) l }
  have h_finite : s.Finite := by
    -- Each valid path from $(0,0)$ to $(m,n)$ can be described by a sequence of moves, either right or down.
    have h_paths_finite : ∀ p q : GridPoint, Set.Finite {l : GridPath | IsValidPath p q l ∧ l.length ≤ m + n} := by
      intro p q;
      -- Each valid path from $(0,0)$ to $(m,n)$ can be described by a sequence of moves, either right or down. The number of such sequences is finite.
      have h_paths_finite : ∀ p q : GridPoint, ∀ k : ℕ, Set.Finite { l : GridPath | IsValidPath p q l ∧ l.length = k } := by
        intro p q k
        induction' k with k ih generalizing p q;
        · refine Set.Finite.subset ( Set.finite_singleton [ ] ) ?_ ; aesop;
        · have h_finite_edges : Set.Finite {e : Edge | is_up_right e ∧ e.1 = p} := by
            exact Set.Finite.subset ( Set.toFinite { ( p, ( p.1 + 1, p.2 ) ), ( p, ( p.1, p.2 + 1 ) ) } ) fun e he => by cases he; aesop;
          refine' Set.Finite.subset ( h_finite_edges.biUnion fun e he => ih e.2 q |> Set.Finite.image fun l => ( e :: l ) ) _;
          intro l hl; rcases hl with ⟨ hl₁, hl₂ ⟩ ; induction' l with e l ih <;> aesop;
          · cases hl₁ ; aesop;
            exact ⟨ h_path, rfl ⟩;
          · cases hl₁ ; aesop;
          · cases hl₁ ; aesop;
      exact Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_Iic ( m + n ) ) fun k hk => h_paths_finite p q k ) fun l hl => by aesop;
    refine h_paths_finite ( 0, 0 ) ( m, n ) |> Set.Finite.subset <| fun l hl => ?_;
    -- By definition of IsValidPath, each path from (0,0) to (m,n) consists of exactly m + n steps.
    have h_length : ∀ p q : GridPoint, ∀ l : GridPath, IsValidPath p q l → l.length = q.1 + q.2 - p.1 - p.2 := by
      intros p q l hl; induction hl <;> aesop;
      rcases h_edge with ( ⟨ h₁, h₂ ⟩ | ⟨ h₁, h₂ ⟩ ) <;> simp_all +decide [ Nat.sub_sub ];
      · have h_length : ∀ p q : GridPoint, ∀ l : GridPath, IsValidPath p q l → p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
          intros p q l hl; induction hl <;> aesop;
          · cases h_edge <;> aesop;
            linarith;
          · cases h_edge <;> aesop;
            linarith;
        grind;
      · rw [ tsub_add_eq_add_tsub ];
        · omega;
        · have h_length : ∀ p q : GridPoint, ∀ l : GridPath, IsValidPath p q l → p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
            intros p q l hl; induction hl <;> aesop;
            · cases h_edge <;> aesop ; linarith;
            · cases h_edge <;> aesop ; linarith;
          linarith [ h_length _ _ _ h_path ];
    exact ⟨ hl, h_length _ _ _ hl ▸ by norm_num ⟩
  h_finite.toFinset

/-
The set of paths from (0,0) to (m,n) is nonempty.
-/
lemma paths_nonempty (m n : ℕ) : (paths m n).Nonempty := by
  -- We'll use induction to prove that there is always a valid path from $(0,0)$ to $(m,n)$.
  induction' m with m ih generalizing n;
  · use List.map ( fun i => ( ( 0, i ), ( 0, i + 1 ) ) ) ( List.range n );
    unfold paths; aesop;
    induction' n with n ih <;> simp_all +decide [ List.range_succ ];
    · constructor;
    · convert IsValidPath.cons _ _ _ _ _ _ using 1;
      rotate_left;
      exact ( 0, 1 );
      exact List.map ( fun i => ( ( 0, i + 1 ), 0, i + 2 ) ) ( List.range n );
      · exact Or.inr ⟨ rfl, rfl ⟩;
      · have h_valid : ∀ (p q : GridPoint) (l : GridPath), IsValidPath p q l → IsValidPath (p.1, p.2 + 1) (q.1, q.2 + 1) (List.map (fun e => ((e.1.1, e.1.2 + 1), (e.2.1, e.2.2 + 1))) l) := by
          intros p q l hl; induction hl <;> aesop;
          · constructor;
          · apply_rules [ IsValidPath.cons ];
            cases h_edge <;> aesop;
            · exact Or.inl ⟨ rfl, rfl ⟩;
            · exact Or.inr ⟨ rfl, rfl ⟩;
        convert h_valid _ _ _ ih using 1;
        induction ( List.range n ) <;> aesop;
      · exact Nat.recOn n ( by norm_num ) fun n ih => by simp_all +decide [ List.range_succ ] ;
  · by_contra h_empty;
    obtain ⟨l, hl⟩ : ∃ l : GridPath, IsValidPath (0, 0) (m, n) l := by
      specialize ih n; unfold paths at ih; aesop;
    have h_path : ∃ l' : GridPath, IsValidPath (m, n) (m + 1, n) l' := by
      exact ⟨ [ ( ( m, n ), ( m + 1, n ) ) ], by exact IsValidPath.cons _ _ _ _ ( by exact Or.inl ⟨ rfl, rfl ⟩ ) ( by exact IsValidPath.nil _ ) ⟩;
    aesop;
    have h_path : ∃ l' : GridPath, IsValidPath (0, 0) (m + 1, n) l' := by
      have h_path : ∀ p q r : GridPoint, ∀ l : GridPath, IsValidPath p q l → ∀ w : GridPath, IsValidPath q r w → ∃ l' : GridPath, IsValidPath p r l' := by
        intros p q r l hl w hw;
        induction hl <;> aesop;
        exact ⟨ ( p_1, q_1 ) :: w_2, by exact IsValidPath.cons _ _ _ _ h_edge h_1 ⟩;
      exact h_path _ _ _ _ hl _ h;
    obtain ⟨ l', hl' ⟩ := h_path;
    replace h_empty := Finset.ext_iff.mp h_empty l'; aesop;
    exact h_empty <| by unfold paths; aesop;

/-
Definition of LPP value.
-/
/-- The Last Passage Percolation value for a given weight function. -/
noncomputable def LPP_value (m n : ℕ) (weights : Edge → ℝ) : ℝ :=
  ((paths m n).image (fun p => (p.map weights).sum)).max' (by simp [paths_nonempty])
