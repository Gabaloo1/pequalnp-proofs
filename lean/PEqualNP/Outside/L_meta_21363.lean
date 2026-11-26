import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search, replayed on the 20 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_21363_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [17, 19]⟩], 20⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21363_aux

open PEqualNP.Outside.L_meta_21363_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21363 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40318 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
