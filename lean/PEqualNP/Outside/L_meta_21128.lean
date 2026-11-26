import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search, replayed on the 20 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_21128_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [4, 15]⟩, ⟨.and, [16, 17]⟩], 18⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21128_aux

open PEqualNP.Outside.L_meta_21128_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21128 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36253 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
