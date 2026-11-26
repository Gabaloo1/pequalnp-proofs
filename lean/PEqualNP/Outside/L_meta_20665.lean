import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20665_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20665_aux

open PEqualNP.Outside.L_meta_20665_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20665 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16124928 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
