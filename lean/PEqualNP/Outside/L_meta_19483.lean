import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_19483_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [6, 15]⟩, ⟨.not, [17]⟩, ⟨.or, [16, 18]⟩], 19⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19483_aux

open PEqualNP.Outside.L_meta_19483_aux in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_19483 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3257437 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨witness, witnessFit, by decide +kernel, ?_⟩
  intro u v
  revert u v
  decide +kernel
