import Mathlib
import PEqualNP.Defs

-- The live-set search and its completeness proof are adapted from
-- lean/PEqualNP/Outside/L_meta_6345.lean in this repository, widened from 64 to 156
-- (true entry, false entry) pairs; the rows, the 10-gate search and the conclusion are new.
-- The last phase of the search (no spare gate left) is done on natural numbers and relies on
-- the kernel recognising repeated states; see the comment above FULL.

namespace PEqualNP.Outside.L_meta_9209

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 312

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 156 := ((x >>> 156) &&& ~~~x).setWidth 156

def cuts (ws : List W) : BitVec 156 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 156) ++ (0 : BitVec 156)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xffffffffffff001001001001001001001001001001001001001, 0xffffff00000000000000e00e00e00e00e00e00e00e00e00e00e00e00e, 0xfff0000000000000000000f00f00f00f00f00f00f00f00f00f00f00f00f0, 0xfffffffff000000000000000000000300300300300300300300300300300300300300, 0xfffffffff000000000000000000000000000000c00c00c00c00c00c00c00c00c00c00c00c00c00, 0xfff000000ffffff000fff000000000000001001001001001001001001001001001001001, 0xfff000000fff000000000000000000000fff012012012012012012012012012012012012012, 0xfff000000fff000000000000000000000fff000024024024024024024024024024024024024024, 0xfff000000548548548548548548548548548548548548548, 0xfff000fff000000000a80a80a80a80a80a80a80a80a80a80a80a80a80]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 156) (w : W) : Prop :=
  w.getLsbD (156 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 156) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (156 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (156 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 156, differs i goal := by
  unfold differs
  decide +kernel

theorem cuts_spec (ws : List W) (i : Fin 156) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 312 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 156)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 312 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 312) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 312) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 312, by simp [possible], by simp [step, GateOp.eval, bit]; decide +kernel⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 312 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 312 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 312 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 312 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide +kernel : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide +kernel : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide +kernel : goal ≠ BitVec.allOnes 312) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 312 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

-- The phase with no spare gate (every remaining gate must merge two live wires into one) is
-- searched on natural numbers, with recursors written out so that the kernel does little work
-- per pair, and with every state rebuilt as a sorted list of numerals before the recursive
-- call, so that the kernel's cache of evaluated terms recognises a state it has already refuted.

def FULL : ℕ := 0xfffffffffffffffffffffffffffffffffffffff

def C312 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def sepN (n : ℕ) : ℕ := Nat.land (Nat.shiftRight n 156) (Nat.sub C312 n)

noncomputable def once : List ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.lor (sepN x) ih)

noncomputable def twice : List ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x l ih => Nat.lor ih (Nat.land (once l) (sepN x)))

noncomputable def thrice : List ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x l ih => Nat.lor ih (Nat.land (twice l) (sepN x)))

noncomputable def ins (z : ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ) [z]
    (fun x tl ih => Bool.rec (motive := fun _ => List ℕ) (x :: ih) (z :: x :: tl) (Nat.ble z x))

noncomputable def sortN : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun x _ ih => ins x ih)

noncomputable def del2 (a b : ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun x _ ih => Bool.rec (motive := fun _ => List ℕ)
      (Bool.rec (motive := fun _ => List ℕ) (x :: ih) ih (Nat.beq x b)) ih (Nat.beq x a))

noncomputable def forceList : List ℕ → (List ℕ → Bool) → Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun f => f [])
    (fun x _ ih f => Nat.rec (motive := fun _ => Bool) (ih (fun l => f (Nat.zero :: l)))
      (fun n _ => ih (fun l => f (Nat.succ n :: l))) x)

noncomputable def memo (next : List ℕ → Bool) (l : List ℕ) : Bool :=
  forceList l (fun l' => Bool.rec (motive := fun _ => Bool) false true (next l'))

noncomputable def hit (next : List ℕ → Bool) (ws : List ℕ) (a b z : ℕ) (cont : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) cont true (memo next (ins z (del2 a b ws)))

def testN (z a1 a2 b : ℕ) : Bool :=
  Nat.beq (Nat.lor (sepN z) (Nat.lor a1 (Nat.land (sepN b) a2))) (sepN z)

noncomputable def inner (next : List ℕ → Bool) (ws : List ℕ) (a a1 a2 : ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih =>
      (fun (c : Bool) => Bool.rec (motive := fun _ => Bool) c (hit next ws a b (Nat.land a b) c)
        (Nat.beq (Nat.lor (sepN (Nat.land a b)) (Nat.lor a1 (Nat.land (sepN b) a2)))
          (sepN (Nat.land a b))))
      (Bool.rec (motive := fun _ => Bool) ih (hit next ws a b (Nat.lor a b) ih)
        (Nat.beq (Nat.lor (sepN (Nat.lor a b)) (Nat.lor a1 (Nat.land (sepN b) a2)))
          (sepN (Nat.lor a b)))))

noncomputable def outer (next : List ℕ → Bool) (ws : List ℕ) (n2 n3 : ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a tl ih => Bool.rec (motive := fun _ => Bool) ih true
      (inner next ws a (Nat.land n2 (sepN a)) (Nat.lor n2 (Nat.land n3 (sepN a))) tl))

noncomputable def node (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  outer next ws (Nat.xor (Nat.land (twice ws) FULL) FULL)
    (Nat.xor (Nat.land (thrice ws) FULL) FULL) ws

noncomputable def isGoal : List ℕ → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x tl _ => List.rec (motive := fun _ => Bool) (Nat.beq x goal.toNat) (fun _ _ _ => false) tl)

noncomputable def strictN : ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) isGoal (fun _ ih ws => node ih ws)

noncomputable def enter (k : ℕ) (ws : List W) : Bool :=
  memo (strictN k) (sortN (ws.map BitVec.toNat))

theorem brec {α : Type} (x y : α) (c : Bool) :
    @Bool.rec (fun _ => α) x y c = if c = true then y else x := by
  cases c <;> rfl

theorem forceList_cons (x : ℕ) (xs : List ℕ) (f : List ℕ → Bool) :
    forceList (x :: xs) f = @Nat.rec (fun _ => Bool) (forceList xs (fun l => f (Nat.zero :: l)))
      (fun n _ => forceList xs (fun l => f (Nat.succ n :: l))) x := rfl

theorem forceList_eq (l : List ℕ) (f : List ℕ → Bool) : forceList l f = f l := by
  induction l generalizing f with
  | nil => rfl
  | cons x xs ih =>
    rw [forceList_cons]
    cases x with
    | zero => exact ih _
    | succ n => exact ih _

theorem memo_eq (next : List ℕ → Bool) (l : List ℕ) : memo next l = next l := by
  unfold memo
  rw [forceList_eq]
  cases next l <;> rfl

theorem ins_cons (z x : ℕ) (tl : List ℕ) : ins z (x :: tl) =
    @Bool.rec (fun _ => List ℕ) (x :: ins z tl) (z :: x :: tl) (Nat.ble z x) := rfl

theorem ins_perm (z : ℕ) (l : List ℕ) : (ins z l).Perm (z :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x tl ih =>
    rw [ins_cons, brec]
    split
    · exact List.Perm.refl _
    · exact (ih.cons x).trans (List.Perm.swap z x tl)

theorem sortN_perm (l : List ℕ) : (sortN l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x tl ih => exact (ins_perm x (sortN tl)).trans (ih.cons x)

theorem del2_cons (a b x : ℕ) (tl : List ℕ) : del2 a b (x :: tl) =
    @Bool.rec (fun _ => List ℕ)
      (@Bool.rec (fun _ => List ℕ) (x :: del2 a b tl) (del2 a b tl) (Nat.beq x b))
      (del2 a b tl) (Nat.beq x a) := rfl

theorem del2_eq (a b : ℕ) (l : List ℕ) :
    del2 a b l = l.filter (fun x => decide (x ≠ a ∧ x ≠ b)) := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
    rw [del2_cons, brec, brec, ih, List.filter_cons]
    by_cases ha : x = a
    · simp [ha]
    · by_cases hb : x = b
      · simp [hb]
      · simp [ha, hb]

theorem del2_perm {ws r : List ℕ} {a b : ℕ} (hn : ws.Nodup) (hp : ws.Perm (a :: b :: r)) :
    (del2 a b ws).Perm r := by
  rw [del2_eq]
  have hn' := hp.nodup_iff.mp hn
  simp only [List.nodup_cons, List.mem_cons, not_or] at hn'
  have h1 := hp.filter (fun x => decide (x ≠ a ∧ x ≠ b))
  have h2 : (a :: b :: r).filter (fun x => decide (x ≠ a ∧ x ≠ b)) = r := by
    rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_neg (by simp)]
    apply List.filter_eq_self.mpr
    intro x hx
    have h3 : x ≠ a := fun h => hn'.1.2 (h ▸ hx)
    have h4 : x ≠ b := fun h => hn'.2.1 (h ▸ hx)
    simp [h3, h4]
  exact h2 ▸ h1

theorem lor_bit (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem land_bit (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

theorem xor_bit (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) :=
  Nat.testBit_xor x y i

theorem full_bit (i : ℕ) : FULL.testBit i = decide (i < 156) := by
  have h : FULL = 2 ^ 156 - 1 := by norm_num [FULL]
  rw [h, Nat.testBit_two_pow_sub_one]

def cnt (i : ℕ) (l : List ℕ) : ℕ := l.countP (fun x => (sepN x).testBit i)

theorem cnt_cons (i x : ℕ) (l : List ℕ) :
    cnt i (x :: l) = cnt i l + if (sepN x).testBit i = true then 1 else 0 :=
  List.countP_cons

theorem once_cons (x : ℕ) (l : List ℕ) : once (x :: l) = Nat.lor (sepN x) (once l) := rfl

theorem twice_cons (x : ℕ) (l : List ℕ) :
    twice (x :: l) = Nat.lor (twice l) (Nat.land (once l) (sepN x)) := rfl

theorem thrice_cons (x : ℕ) (l : List ℕ) :
    thrice (x :: l) = Nat.lor (thrice l) (Nat.land (twice l) (sepN x)) := rfl

theorem once_bit (i : ℕ) (l : List ℕ) : (once l).testBit i = decide (1 ≤ cnt i l) := by
  induction l with
  | nil => simp [once, cnt]
  | cons x l ih =>
    rw [once_cons, lor_bit, ih, cnt_cons]
    cases (sepN x).testBit i <;> simp

theorem twice_bit (i : ℕ) (l : List ℕ) : (twice l).testBit i = decide (2 ≤ cnt i l) := by
  induction l with
  | nil => simp [twice, cnt]
  | cons x l ih =>
    rw [twice_cons, lor_bit, land_bit, ih, once_bit, cnt_cons]
    cases (sepN x).testBit i
    · simp
    · simp
      omega

theorem thrice_bit (i : ℕ) (l : List ℕ) : (thrice l).testBit i = decide (3 ≤ cnt i l) := by
  induction l with
  | nil => simp [thrice, cnt]
  | cons x l ih =>
    rw [thrice_cons, lor_bit, land_bit, ih, twice_bit, cnt_cons]
    cases (sepN x).testBit i
    · simp
    · simp
      omega

theorem test_ok {ws r : List ℕ} {a b z : ℕ} (hp : ws.Perm (a :: b :: r))
    (hc : once (z :: r) = FULL) :
    testN z (Nat.land (Nat.xor (Nat.land (twice ws) FULL) FULL) (sepN a))
      (Nat.lor (Nat.xor (Nat.land (twice ws) FULL) FULL)
        (Nat.land (Nat.xor (Nat.land (thrice ws) FULL) FULL) (sepN a))) b = true := by
  have key : Nat.lor (sepN z) (Nat.lor
      (Nat.land (Nat.xor (Nat.land (twice ws) FULL) FULL) (sepN a))
      (Nat.land (sepN b) (Nat.lor (Nat.xor (Nat.land (twice ws) FULL) FULL)
        (Nat.land (Nat.xor (Nat.land (thrice ws) FULL) FULL) (sepN a))))) = sepN z := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hcnt : cnt i ws = cnt i (a :: b :: r) := hp.countP_eq _
    have hci := congrArg (fun n => n.testBit i) hc
    simp only [once_cons, lor_bit, land_bit, xor_bit, full_bit, once_bit, twice_bit, thrice_bit,
      hcnt, cnt_cons] at hci ⊢
    by_cases hi : i < 156 <;>
      cases ha : (sepN a).testBit i <;> cases hb : (sepN b).testBit i <;>
      cases hz : (sepN z).testBit i <;> simp_all
  unfold testN
  rw [key]
  exact Nat.beq_refl _

theorem c312_eq : C312 = 2 ^ 312 - 1 := by decide +kernel

theorem sepN_toNat (w : W) : sepN w.toNat = (sep w).toNat := by
  have h1 : w.toNat >>> 156 < 2 ^ 156 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by have := w.isLt; omega)
  simp only [sep, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_not]
  rw [← c312_eq]
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left h1)).symm

theorem once_map (l : List W) : once (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    show Nat.lor (sepN w.toNat) (once (l.map BitVec.toNat)) = (sep w ||| cuts l).toNat
    rw [BitVec.toNat_or, ih, sepN_toNat]
    rfl

theorem hit_eq (next : List ℕ → Bool) (ws : List ℕ) (a b z : ℕ) (cont : Bool) :
    hit next ws a b z cont = (next (ins z (del2 a b ws)) || cont) := by
  unfold hit
  rw [brec, memo_eq]
  cases next (ins z (del2 a b ws)) <;> simp

theorem inner_cons (next : List ℕ → Bool) (ws : List ℕ) (a a1 a2 b : ℕ) (tl : List ℕ) :
    inner next ws a a1 a2 (b :: tl) =
      ((testN (Nat.land a b) a1 a2 b && next (ins (Nat.land a b) (del2 a b ws))) ||
       (testN (Nat.lor a b) a1 a2 b && next (ins (Nat.lor a b) (del2 a b ws))) ||
       inner next ws a a1 a2 tl) := by
  have h : inner next ws a a1 a2 (b :: tl) =
      @Bool.rec (fun _ => Bool)
        (@Bool.rec (fun _ => Bool) (inner next ws a a1 a2 tl)
          (hit next ws a b (Nat.lor a b) (inner next ws a a1 a2 tl)) (testN (Nat.lor a b) a1 a2 b))
        (hit next ws a b (Nat.land a b)
          (@Bool.rec (fun _ => Bool) (inner next ws a a1 a2 tl)
            (hit next ws a b (Nat.lor a b) (inner next ws a a1 a2 tl))
            (testN (Nat.lor a b) a1 a2 b)))
        (testN (Nat.land a b) a1 a2 b) := rfl
  rw [h, brec, brec, hit_eq, hit_eq]
  generalize testN (Nat.land a b) a1 a2 b = t1
  generalize testN (Nat.lor a b) a1 a2 b = t2
  generalize next (ins (Nat.land a b) (del2 a b ws)) = n1
  generalize next (ins (Nat.lor a b) (del2 a b ws)) = n2
  generalize inner next ws a a1 a2 tl = i
  cases t1 <;> cases t2 <;> cases n1 <;> cases n2 <;> cases i <;> rfl

theorem inner_true (next : List ℕ → Bool) (ws : List ℕ) (a a1 a2 : ℕ) {b : ℕ} {l : List ℕ}
    (hb : b ∈ l)
    (hok : (testN (Nat.land a b) a1 a2 b && next (ins (Nat.land a b) (del2 a b ws))) = true ∨
      (testN (Nat.lor a b) a1 a2 b && next (ins (Nat.lor a b) (del2 a b ws))) = true) :
    inner next ws a a1 a2 l = true := by
  induction l with
  | nil => simp at hb
  | cons x tl ih =>
    rw [inner_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · rcases hok with h | h
      · rw [h]
        rfl
      · rw [h]
        simp only [Bool.or_true, Bool.true_or]
    · rw [ih hb]
      simp only [Bool.or_true]

theorem outer_cons (next : List ℕ → Bool) (ws : List ℕ) (n2 n3 a : ℕ) (tl : List ℕ) :
    outer next ws n2 n3 (a :: tl) =
      (inner next ws a (Nat.land n2 (sepN a)) (Nat.lor n2 (Nat.land n3 (sepN a))) tl ||
        outer next ws n2 n3 tl) := by
  have h : outer next ws n2 n3 (a :: tl) = @Bool.rec (fun _ => Bool) (outer next ws n2 n3 tl) true
      (inner next ws a (Nat.land n2 (sepN a)) (Nat.lor n2 (Nat.land n3 (sepN a))) tl) := rfl
  rw [h, brec]
  cases inner next ws a (Nat.land n2 (sepN a)) (Nat.lor n2 (Nat.land n3 (sepN a))) tl <;> simp

theorem outer_true (next : List ℕ → Bool) (ws : List ℕ) (n2 n3 : ℕ) {a : ℕ} {tl l : List ℕ}
    (hs : (a :: tl) <:+ l)
    (hi : inner next ws a (Nat.land n2 (sepN a)) (Nat.lor n2 (Nat.land n3 (sepN a))) tl = true) :
    outer next ws n2 n3 l = true := by
  induction l with
  | nil => simp at hs
  | cons x t ih =>
    rw [outer_cons]
    rcases List.suffix_cons_iff.mp hs with h | h
    · injection h with h1 h2
      subst h1 h2
      rw [hi]
      rfl
    · rw [ih h]
      simp only [Bool.or_true]

theorem find_pair {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ tl, ((a :: tl) <:+ l ∧ b ∈ tl) ∨ ((b :: tl) <:+ l ∧ a ∈ tl) := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    by_cases hxa : x = a
    · subst hxa
      exact ⟨t, .inl ⟨List.suffix_refl _, (List.mem_cons.mp hb).resolve_left (Ne.symm hab)⟩⟩
    · by_cases hxb : x = b
      · subst hxb
        exact ⟨t, .inr ⟨List.suffix_refl _, (List.mem_cons.mp ha).resolve_left hab⟩⟩
      · obtain ⟨tl, h⟩ := ih ((List.mem_cons.mp ha).resolve_left (fun h => hxa h.symm))
          ((List.mem_cons.mp hb).resolve_left (fun h => hxb h.symm))
        exact ⟨tl, h.imp (fun h => ⟨h.1.trans (List.suffix_cons x t), h.2⟩)
          (fun h => ⟨h.1.trans (List.suffix_cons x t), h.2⟩)⟩

theorem node_half (next : List ℕ → Bool) {ws r tl : List ℕ} {x y z : ℕ} (hn : ws.Nodup)
    (hp : ws.Perm (x :: y :: r)) (hz : z = Nat.land x y ∨ z = Nat.lor x y)
    (hc : once (z :: r) = FULL) (hnext : ∀ l, l.Perm (z :: r) → next l = true)
    (hs : (x :: tl) <:+ ws) (hy : y ∈ tl) : node next ws = true := by
  unfold node
  apply outer_true next ws _ _ hs
  apply inner_true next ws _ _ _ hy
  have hchild : next (ins z (del2 x y ws)) = true :=
    hnext _ ((ins_perm z _).trans ((del2_perm hn hp).cons z))
  have ht := test_ok (z := z) hp hc
  rcases hz with rfl | rfl
  · left; rw [ht, hchild]; rfl
  · right; rw [ht, hchild]; rfl

theorem node_complete (next : List ℕ → Bool) {ws r : List ℕ} {a b z : ℕ} (hn : ws.Nodup)
    (hp : ws.Perm (a :: b :: r)) (hz : z = Nat.land a b ∨ z = Nat.lor a b)
    (hc : once (z :: r) = FULL) (hnext : ∀ l, l.Perm (z :: r) → next l = true) :
    node next ws = true := by
  have hn' := hp.nodup_iff.mp hn
  have hab : a ≠ b := by
    intro h
    subst h
    simp at hn'
  have ha : a ∈ ws := hp.mem_iff.mpr (by simp)
  have hb : b ∈ ws := hp.mem_iff.mpr (by simp)
  obtain ⟨tl, h | h⟩ := find_pair ha hb hab
  · exact node_half next hn hp hz hc hnext h.1 h.2
  · refine node_half next hn (hp.trans (List.Perm.swap b a r)) ?_ hc hnext h.1 h.2
    rcases hz with rfl | rfl
    · exact .inl (Nat.and_comm a b)
    · exact .inr (Nat.or_comm a b)

theorem isGoal_goal : isGoal [goal.toNat] = true := by
  show Nat.beq goal.toNat goal.toNat = true
  simp

theorem neg_one_toNat : (-1 : BitVec 156).toNat = FULL := by decide

theorem strict_complete (k : ℕ) : ∀ ws : List W, ws.Nodup → ws.length = k + 1 →
    live basicOps goal k ws.toFinset → ∀ l : List ℕ, l.Perm (ws.map BitVec.toNat) →
    strictN k l = true := by
  induction k with
  | zero =>
    intro ws hn _ h l hl
    have hws : ws = [goal] := singleton_list hn h
    subst hws
    have hl1 : l = [goal.toNat] := List.perm_singleton.mp hl
    subst hl1
    exact isGoal_goal
  | succ k ih =>
    intro ws hn hlen h l hl
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · have hws := singleton_list hn done
      rw [hws] at hlen
      simp at hlen
    · have hzn : z ∉ needed := fun hm => hout (by rw [hs]; simp [hm])
      have hc1 := live_card tail
      rw [Finset.card_insert_of_notMem hzn] at hc1
      have hc2 : ws.toFinset.card = k + 2 := by rw [List.toFinset_card_of_nodup hn, hlen]
      rw [hs] at hc2
      have hbn : b ∉ needed := by
        intro hm
        rw [Finset.insert_eq_of_mem hm] at hc2
        have := Finset.card_insert_le a needed
        omega
      have han : a ∉ insert b needed := by
        intro hm
        rw [Finset.insert_eq_of_mem hm] at hc2
        have := Finset.card_insert_le b needed
        omega
      rw [Finset.card_insert_of_notMem han, Finset.card_insert_of_notMem hbn] at hc2
      have hrn : needed.toList.Nodup := needed.nodup_toList
      have hzr : z ∉ needed.toList := fun hm => hzn (Finset.mem_toList.mp hm)
      have hnd : (z :: needed.toList).Nodup := List.nodup_cons.mpr ⟨hzr, hrn⟩
      have hfin : (z :: needed.toList).toFinset = insert z needed := by simp
      have hlive : live basicOps goal k (z :: needed.toList).toFinset := hfin ▸ tail
      have hlen' : (z :: needed.toList).length = k + 1 := by
        simp only [List.length_cons, Finset.length_toList]
        omega
      have hperm : ws.Perm (a :: b :: needed.toList) := by
        apply List.perm_of_nodup_nodup_toFinset_eq hn
        · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrn⟩⟩
          · intro hm
            apply han
            rcases List.mem_cons.mp hm with h | h
            · simp [h]
            · simp [Finset.mem_toList.mp h]
          · exact fun hm => hbn (Finset.mem_toList.mp hm)
        · rw [hs]
          simp
      have hpN : l.Perm (a.toNat :: b.toNat :: needed.toList.map BitVec.toNat) :=
        hl.trans (hperm.map _)
      have hlN : l.Nodup := hl.nodup_iff.mpr (hn.map (fun _ _ h => BitVec.eq_of_toNat_eq h))
      have hzN : z.toNat = Nat.land a.toNat b.toNat ∨ z.toNat = Nat.lor a.toNat b.toNat := by
        simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
          or_false] at hz
        rcases hz with rfl | rfl
        · exact .inl (BitVec.toNat_and _ _)
        · exact .inr (BitVec.toNat_or _ _)
      have hcN : once (z.toNat :: needed.toList.map BitVec.toNat) = FULL := by
        have h1 := cuts_full hlive
        have h2 := once_map (z :: needed.toList)
        rw [h1] at h2
        exact h2.trans neg_one_toNat
      exact node_complete (strictN k) hlN hpN hzN hcN
        (fun l' hl' => ih (z :: needed.toList) hnd hlen' hlive l' hl')

theorem enter_complete (k : ℕ) (ws : List W) (hn : ws.Nodup) (hlen : ws.length = k + 1)
    (h : live basicOps goal k ws.toFinset) : enter k ws = true := by
  unfold enter
  rw [memo_eq]
  exact strict_complete k ws hn hlen h _ (sortN_perm _)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

-- The same device for the phase with spare gates: the recursive call is made on the sorted
-- list of forced numerals, so that a repeated state is a repeated term.
noncomputable def canonW (l : List W) : List W :=
  (sortN (l.map BitVec.toNat)).map (BitVec.ofNat 312)

noncomputable def canonCall (f : ℕ → List W → Bool) (e : ℕ) (l : List W) : Bool :=
  Nat.rec (motive := fun _ => Bool)
    (forceList (sortN (l.map BitVec.toNat)) (fun l' => Bool.rec (motive := fun _ => Bool)
      false true (f Nat.zero (l'.map (BitVec.ofNat 312)))))
    (fun n _ => forceList (sortN (l.map BitVec.toNat)) (fun l' =>
      Bool.rec (motive := fun _ => Bool) false true (f (Nat.succ n) (l'.map (BitVec.ofNat 312)))))
    e

theorem bid (b : Bool) : @Bool.rec (fun _ => Bool) false true b = b := by
  cases b <;> rfl

theorem canonCall_eq (f : ℕ → List W → Bool) (e : ℕ) (l : List W) :
    canonCall f e l = f e (canonW l) := by
  cases e with
  | zero =>
    exact (forceList_eq (sortN (l.map BitVec.toNat)) (fun l' =>
      @Bool.rec (fun _ => Bool) false true (f Nat.zero (l'.map (BitVec.ofNat 312))))).trans (bid _)
  | succ n =>
    exact (forceList_eq (sortN (l.map BitVec.toNat)) (fun l' =>
      @Bool.rec (fun _ => Bool) false true (f (Nat.succ n) (l'.map (BitVec.ofNat 312))))).trans
        (bid _)

theorem canonW_perm (l : List W) : (canonW l).Perm l := by
  have h := (sortN_perm (l.map BitVec.toNat)).map (BitVec.ofNat 312)
  have e : (l.map BitVec.toNat).map (BitVec.ofNat 312) = l := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro x _
    simp
  have h2 : (canonW l).Perm ((l.map BitVec.toNat).map (BitVec.ofNat 312)) := h
  rw [e] at h2
  exact h2

noncomputable def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, 0, ws => enter (k + 1) ws
  | k + 1, extra + 1, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) =>
      dispatch (extra + 1) (fun e l => canonCall (optimized k) e l) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    cases extra with
    | zero =>
      show enter (k + 1) ws = true
      exact enter_complete (k + 1) ws hn (by omega) h
    | succ e =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch (e + 1) (fun e l => canonCall (optimized k) e l) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := e + 1) (fun e l => canonCall (optimized k) e l)
          hop hk (by omega) (by omega) (cuts_full hl)
        show canonCall (optimized k) (k - kept.length) (z :: kept) = true
        rw [canonCall_eq]
        have hpc := canonW_perm (z :: kept)
        have hfs : (canonW (z :: kept)).toFinset = (z :: kept).toFinset :=
          List.toFinset_eq_of_perm _ _ hpc
        apply ih _ _ (hpc.nodup_iff.mpr hnd) _ (hfs ▸ hl)
        rw [hpc.length_eq]
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 5 → Fin 5 → Bool := fun u v => (7571006 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 4), (2, 0), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)]

def negL : List (Fin 5 × Fin 5) :=
  [(0, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 3), (4, 4)]

def samp (k : Fin 312) : Fin 5 × Fin 5 :=
  if k.val < 156 then negL.getD (k.val % 12) (0, 0) else posL.getD ((k.val - 156) / 12) (0, 0)

theorem input_rows : ∀ k : Fin 312,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 312, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 312) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

theorem inputs_length : inputs.length = 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem front_small : (inputs.sublists.filter (fun l => decide (l.length < 10))).all
    (fun l => cuts l != -1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem full_none : optimized 10 1 inputs = false := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 10 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 10 l (11 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hsl : l.Sublist inputs := List.filter_sublist
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr hsl
  by_cases hlen : l.length < 10
  · have hrow := List.all_eq_true.mp front_small l
      (List.mem_filter.mpr ⟨hmem, by simpa using hlen⟩)
    rw [cuts_full (hlS ▸ hl3)] at hrow
    simp at hrow
  · have hle := hsl.length_le
    rw [inputs_length] at hle
    have heq : l = inputs := hsl.eq_of_length (by rw [inputs_length]; omega)
    rw [heq, inputs_length] at hsearch
    have hf : optimized 10 1 inputs = false := full_none
    have h1 : (11 - 10 : ℕ) = 1 := rfl
    rw [h1, hf] at hsearch
    exact Bool.noConfusion hsearch

end PEqualNP.Outside.L_meta_9209

theorem PEqualNP.Outside.L_meta_9209 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7571006 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_9209.no_small C hm hs hr
