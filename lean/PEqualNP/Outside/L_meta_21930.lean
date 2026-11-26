import Mathlib
import PEqualNP.Defs

-- Witness circuit named in the step, replayed on the 21 inputs with one or two wires on.

namespace PEqualNP.Outside.L_meta_21930_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21930_aux

open PEqualNP.Outside.L_meta_21930_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21930 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34092 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
