import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search, replayed on the 20 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_21124_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21124_aux

open PEqualNP.Outside.L_meta_21124_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21124 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36092 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
