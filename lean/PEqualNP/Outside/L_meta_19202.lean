import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 16 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_19202_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

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

end PEqualNP.Outside.L_meta_19202_aux

open PEqualNP.Outside.L_meta_19202_aux in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_19202 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4831 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨witness, witnessFit, by decide +kernel, ?_⟩
  intro u v
  revert u v
  decide +kernel
