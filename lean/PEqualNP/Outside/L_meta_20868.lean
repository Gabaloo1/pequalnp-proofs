import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20868_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [2, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20868_aux

open PEqualNP.Outside.L_meta_20868_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20868 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31328289 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
