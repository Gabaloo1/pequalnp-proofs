import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23955_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- SECTION fold. The wire fold lemmas below (step, W, W_cons, step_len, W_length, getD_app_lt,
-- getD_app_len, getD_ge, step_lt, step_last, W_prefix, W_ge, W_gate) are copied from the merged
-- proof PEqualNP.Outside.L_meta_19198 (fragments fold and mono), credit to its authors.

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := W_length C.gates x

-- SECTION oneEach (copied from the work file of the silent wires step).

theorem getD_app_lt' {α : Type} (l l2 : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge' {α : Type} (l l2 : List α) (d : α) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l2).getD i d = l2.getD (i - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem ofFn_getD' {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The wire values of `oneEach u v`: on exactly at wire `u` and wire `n + v`. -/
theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold PEqualNP.Represents.oneEach
  by_cases hi : i < n
  · rw [getD_app_lt' _ _ _ _ (by rw [List.length_ofFn]; exact hi), ofFn_getD' _ i hi]
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff]
    simp only []
    omega
  · rw [getD_app_ge' _ _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn]
    by_cases hi2 : i - n < m
    · rw [ofFn_getD' _ (i - n) hi2]
      apply decide_eq_decide.mpr
      rw [Fin.ext_iff]
      simp only []
      omega
    · rw [getD_ge _ _ (by rw [List.length_ofFn]; omega)]
      symm
      rw [decide_eq_false_iff_not]
      omega

-- SECTION rename. The renaming of wires.

/-- The new number of old wire `w`: an old input wire `w < N` goes to `ρ w`, old gate wire `N + j`
(`j < G`) goes to `N' + j`, and every other number goes to `N' + G`, beyond the last new wire. -/
def renWire (N N' G : ℕ) (ρ : ℕ → ℕ) (w : ℕ) : ℕ :=
  if w < N then ρ w else if w < N + G then N' + (w - N) else N' + G

/-- A gate with its listed wires renumbered. -/
def renGate (N N' G : ℕ) (ρ : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renWire N N' G ρ)⟩

/-- The circuit `C` (meant for `N` input wires) with its wires renumbered for `N'` input wires. -/
def rename (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renGate N N' C.gates.length ρ), renWire N N' C.gates.length ρ C.output⟩

theorem rename_gates_length (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) :
    (rename N N' ρ C).gates.length = C.gates.length := by
  simp [rename]

/-- (b) the size is kept. -/
theorem rename_size (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) :
    (rename N N' ρ C).size = C.size := rename_gates_length N N' ρ C

/-- (b) AND/OR gates of at most two inputs are kept. -/
theorem rename_monotone2 (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (rename N N' ρ C) := by
  intro g hg
  have hg' : g ∈ C.gates.map (renGate N N' C.gates.length ρ) := hg
  rw [List.mem_map] at hg'
  obtain ⟨g0, hg0, rfl⟩ := hg'
  show g0.op ∈ _ ∧ (g0.inputs.map (renWire N N' C.gates.length ρ)).length ≤ 2
  rw [List.length_map]
  exact h g0 hg0

/-- (b) AND/OR/NOT gates of at most two inputs are kept. -/
theorem rename_fanInTwo (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (rename N N' ρ C) := by
  intro g hg
  have hg' : g ∈ C.gates.map (renGate N N' C.gates.length ρ) := hg
  rw [List.mem_map] at hg'
  obtain ⟨g0, hg0, rfl⟩ := hg'
  show g0.op ∈ _ ∧ (g0.inputs.map (renWire N N' C.gates.length ρ)).length ≤ 2
  rw [List.length_map]
  exact h g0 hg0

/-- What gate `j` reads at a listed wire `w`, before and after the renaming, given that the earlier
gate wires agree. With `j = C.gates.length` this is the value of any wire number. -/
theorem rename_read (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) (xs xs' : List Bool)
    (hx : xs.length = N) (hx' : xs'.length = N')
    (hρ : ∀ i, i < N → (ρ i < N' ∨ N' + C.gates.length ≤ ρ i) ∧
      xs'.getD (ρ i) false = xs.getD i false)
    (j : ℕ) (hj : j ≤ C.gates.length)
    (ih : ∀ k, k < j → ((rename N N' ρ C).wires xs').getD (N' + k) false =
      (C.wires xs).getD (N + k) false) (w : ℕ) :
    (if renWire N N' C.gates.length ρ w < N' + j then
      ((rename N N' ρ C).wires xs').getD (renWire N N' C.gates.length ρ w) false else false) =
    (if w < N + j then (C.wires xs).getD w false else false) := by
  by_cases h1 : w < N
  · have e : renWire N N' C.gates.length ρ w = ρ w := ite_eq_left h1
    rw [e, ite_eq_left (show w < N + j by omega)]
    obtain ⟨hr, hv⟩ := hρ w h1
    have old : (C.wires xs).getD w false = xs.getD w false := W_prefix _ _ _ (by omega)
    rw [old, ← hv]
    rcases hr with hr | hr
    · rw [ite_eq_left (show ρ w < N' + j by omega)]
      exact W_prefix _ _ _ (by omega)
    · rw [ite_eq_right (show ¬ ρ w < N' + j by omega)]
      exact (getD_ge _ _ (by omega)).symm
  · by_cases h2 : w < N + C.gates.length
    · have e : renWire N N' C.gates.length ρ w = N' + (w - N) := by
        unfold renWire; rw [ite_eq_right h1, ite_eq_left h2]
      rw [e]
      by_cases h3 : w < N + j
      · rw [ite_eq_left h3, ite_eq_left (show N' + (w - N) < N' + j by omega)]
        rw [ih (w - N) (by omega)]
        congr 1
        omega
      · rw [ite_eq_right h3, ite_eq_right (show ¬ N' + (w - N) < N' + j by omega)]
    · have e : renWire N N' C.gates.length ρ w = N' + C.gates.length := by
        unfold renWire; rw [ite_eq_right h1, ite_eq_right h2]
      rw [e, ite_eq_right (show ¬ N' + C.gates.length < N' + j by omega),
        ite_eq_right (show ¬ w < N + j by omega)]

/-- (a) every gate wire agrees: new gate wire `N' + j` carries the value of old gate wire
`N + j`. The hypothesis on `ρ`: an old input wire goes to a new input wire carrying the same value,
or to a number beyond the last new wire, in which case the old wire must be off. -/
theorem rename_wire (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) (xs xs' : List Bool)
    (hx : xs.length = N) (hx' : xs'.length = N')
    (hρ : ∀ i, i < N → (ρ i < N' ∨ N' + C.gates.length ≤ ρ i) ∧
      xs'.getD (ρ i) false = xs.getD i false) :
    ∀ j, j < C.gates.length →
      ((rename N N' ρ C).wires xs').getD (N' + j) false = (C.wires xs).getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hj' : j < (rename N N' ρ C).gates.length := by
      rw [rename_gates_length]; exact hj
    have h1 := W_gate (rename N N' ρ C).gates xs' j hj'
    have h2 := W_gate C.gates xs j hj
    rw [hx'] at h1
    rw [hx] at h2
    have hg : (rename N N' ρ C).gates[j] = renGate N N' C.gates.length ρ C.gates[j] := by
      simp [rename]
    rw [wires_eq_W, wires_eq_W, h1, h2, hg]
    show C.gates[j].op.eval ((C.gates[j].inputs.map (renWire N N' C.gates.length ρ)).map _) = _
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro w _
    exact rename_read N N' ρ C xs xs' hx hx' hρ j (le_of_lt hj)
      (fun k hk => ih k hk (by omega)) w

/-- (a) every wire agrees: new wire `renWire w` carries the value of old wire `w`. -/
theorem rename_val (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) (xs xs' : List Bool)
    (hx : xs.length = N) (hx' : xs'.length = N')
    (hρ : ∀ i, i < N → (ρ i < N' ∨ N' + C.gates.length ≤ ρ i) ∧
      xs'.getD (ρ i) false = xs.getD i false) (w : ℕ) :
    ((rename N N' ρ C).wires xs').getD (renWire N N' C.gates.length ρ w) false =
      (C.wires xs).getD w false := by
  have key := rename_read N N' ρ C xs xs' hx hx' hρ C.gates.length (le_refl _)
    (rename_wire N N' ρ C xs xs' hx hx' hρ) w
  have l1 : ((rename N N' ρ C).wires xs').length = N' + C.gates.length := by
    rw [wires_length, rename_gates_length, hx']
  have l2 : (C.wires xs).length = N + C.gates.length := by
    rw [wires_length, hx]
  by_cases a : renWire N N' C.gates.length ρ w < N' + C.gates.length
  · rw [ite_eq_left a] at key
    rw [key]
    by_cases b : w < N + C.gates.length
    · rw [ite_eq_left b]
    · rw [ite_eq_right b]; exact (getD_ge _ _ (by omega)).symm
  · rw [ite_eq_right a] at key
    rw [getD_ge _ _ (by omega)]
    by_cases b : w < N + C.gates.length
    · rw [ite_eq_left b] at key; exact key
    · exact (getD_ge _ _ (by omega)).symm

/-- (a) the renamed circuit on the new input has the value of the old circuit on the old input. -/
theorem rename_eval (N N' : ℕ) (ρ : ℕ → ℕ) (C : Circuit) (xs xs' : List Bool)
    (hx : xs.length = N) (hx' : xs'.length = N')
    (hρ : ∀ i, i < N → (ρ i < N' ∨ N' + C.gates.length ≤ ρ i) ∧
      xs'.getD (ρ i) false = xs.getD i false) :
    (rename N N' ρ C).eval xs' = C.eval xs :=
  rename_val N N' ρ C xs xs' hx hx' hρ C.output

-- SECTION restrict. The renaming that restricts a represented graph to chosen rows and columns.

/-- Old row wire `f u` goes to new row wire `u`, old column wire `n + g v` goes to new column wire
`n' + v`, and every other number goes to `n' + m' + G`, beyond the last new wire. -/
noncomputable def rho (n n' m' G : ℕ) {m : ℕ} (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (i : ℕ) : ℕ :=
  if h : ∃ u : Fin n', (f u).val = i then (Classical.choose h).val
  else if h : ∃ v : Fin m', n + (g v).val = i then n' + (Classical.choose h).val
  else n' + m' + G

theorem rho_spec (n m n' m' G : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) (u : Fin n') (v : Fin m') (i : ℕ) :
    (rho n n' m' G f g i < n' + m' ∨ n' + m' + G ≤ rho n n' m' G f g i) ∧
    (PEqualNP.Represents.oneEach u v).getD (rho n n' m' G f g i) false =
      (PEqualNP.Represents.oneEach (f u) (g v)).getD i false := by
  have hu := u.isLt
  have hv := v.isLt
  have hfu := (f u).isLt
  rw [oneEach_getD, oneEach_getD]
  unfold rho
  by_cases h1 : ∃ u0 : Fin n', (f u0).val = i
  · rw [dite_eq_left h1]
    have hs := Classical.choose_spec h1
    have hlt := (Classical.choose h1).isLt
    refine ⟨Or.inl (by omega), ?_⟩
    apply decide_eq_decide.mpr
    constructor
    · intro h
      rcases h with h | h
      · left
        have e : Classical.choose h1 = u := Fin.ext h
        rw [← hs, e]
      · omega
    · intro h
      rcases h with h | h
      · left
        have e : f (Classical.choose h1) = f u := Fin.ext (by omega)
        exact congrArg Fin.val (hf e)
      · have := (f (Classical.choose h1)).isLt
        omega
  · rw [dite_eq_right h1]
    by_cases h2 : ∃ v0 : Fin m', n + (g v0).val = i
    · rw [dite_eq_left h2]
      have hs := Classical.choose_spec h2
      have hlt := (Classical.choose h2).isLt
      refine ⟨Or.inl (by omega), ?_⟩
      apply decide_eq_decide.mpr
      constructor
      · intro h
        rcases h with h | h
        · omega
        · right
          have e : Classical.choose h2 = v := Fin.ext (by omega)
          rw [← hs, e]
      · intro h
        rcases h with h | h
        · exact absurd ⟨u, h.symm⟩ h1
        · right
          have e : g (Classical.choose h2) = g v := Fin.ext (by omega)
          have e2 := congrArg Fin.val (hg e)
          omega
    · rw [dite_eq_right h2]
      refine ⟨Or.inr (le_refl _), ?_⟩
      apply decide_eq_decide.mpr
      constructor
      · intro h
        omega
      · intro h
        rcases h with h | h
        · exact absurd ⟨u, h.symm⟩ h1
        · exact absurd ⟨v, h.symm⟩ h2

/-- The restricted circuit. -/
noncomputable def restrict (n m n' m' : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (C : Circuit) : Circuit :=
  rename (n + m) (n' + m') (rho n n' m' C.gates.length f g) C

/-- (c) the restricted circuit at `oneEach u v` has the value of `C` at `oneEach (f u) (g v)`. -/
theorem restrict_eval (n m n' m' : ℕ) (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) (C : Circuit)
    (u : Fin n') (v : Fin m') :
    (restrict n m n' m' f g C).eval (PEqualNP.Represents.oneEach u v) =
      C.eval (PEqualNP.Represents.oneEach (f u) (g v)) :=
  rename_eval (n + m) (n' + m') (rho n n' m' C.gates.length f g) C _ _
    (oneEach_length (f u) (g v)) (oneEach_length u v)
    (fun i _ => rho_spec n m n' m' C.gates.length f g hf hg u v i)

/-- (c) the restricted circuit represents the restricted graph. -/
theorem restrict_represents (n m n' m' : ℕ) (A : Fin n → Fin m → Bool)
    (f : Fin n' → Fin n) (g : Fin m' → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g) (C : Circuit)
    (hC : PEqualNP.Represents.Represents A C) :
    PEqualNP.Represents.Represents (fun u v => A (f u) (g v)) (restrict n m n' m' f g C) := by
  intro u v
  rw [restrict_eval n m n' m' f g hf hg C u v]
  exact hC (f u) (g v)

/-- (c) THE RESTRICTION LEMMA, AND/OR circuits. -/
theorem restriction_mono : ∀ (n m n' m' s : ℕ) (A : Fin n → Fin m → Bool)
    (f : Fin n' → Fin n) (g : Fin m' → Fin m),
    Function.Injective f → Function.Injective g →
    PEqualNP.Represents.RepSizeAtMost A s →
    PEqualNP.Represents.RepSizeAtMost (fun u v => A (f u) (g v)) s := by
  intro n m n' m' s A f g hf hg h
  obtain ⟨C, hmono, hsize, hrep⟩ := h
  refine ⟨restrict n m n' m' f g C, rename_monotone2 _ _ _ C hmono, ?_,
    restrict_represents n m n' m' A f g hf hg C hrep⟩
  have e : (restrict n m n' m' f g C).size = C.size := rename_size _ _ _ C
  rw [e]
  exact hsize

/-- (c) THE RESTRICTION LEMMA, AND/OR/NOT circuits. -/
theorem restriction_general : ∀ (n m n' m' s : ℕ) (A : Fin n → Fin m → Bool)
    (f : Fin n' → Fin n) (g : Fin m' → Fin m),
    Function.Injective f → Function.Injective g →
    (∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) →
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
      PEqualNP.Represents.Represents (fun u v => A (f u) (g v)) C := by
  intro n m n' m' s A f g hf hg h
  obtain ⟨C, hfan, hsize, hrep⟩ := h
  refine ⟨restrict n m n' m' f g C, rename_fanInTwo _ _ _ C hfan, ?_,
    restrict_represents n m n' m' A f g hf hg C hrep⟩
  have e : (restrict n m n' m' f g C).size = C.size := rename_size _ _ _ C
  rw [e]
  exact hsize

end PEqualNP.Outside.L_meta_23955_aux

theorem PEqualNP.Outside.L_meta_23955 : (∀ (n m n' m' : ℕ) (A : Fin n → Fin m → Bool) (f : Fin n' → Fin n) (g : Fin m' → Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective f → Function.Injective g → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧ PEqualNP.Represents.Represents (fun (u : Fin n') (v : Fin m') => A (f u) (g v)) C') := by
  intro n m n' m' A f g C hf hg hC hrep
  obtain ⟨D, h1, h2, h3⟩ := PEqualNP.Outside.L_meta_23955_aux.restriction_general n m n' m' C.size A f g hf hg ⟨C, hC, le_refl _, hrep⟩
  exact ⟨D, h1, h2, h3⟩
