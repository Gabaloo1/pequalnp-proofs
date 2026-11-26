import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20696_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [11, 16]⟩], 17⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20696_aux

open PEqualNP.Outside.L_meta_20696_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20696 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16201760 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
