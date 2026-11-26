import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 64 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_19937_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [8, 13]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [13, 19]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [11, 24]⟩, ⟨.and, [2, 25]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [3, 27]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [9, 17]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [26, 37]⟩, ⟨.or, [28, 38]⟩, ⟨.or, [30, 39]⟩, ⟨.or, [32, 40]⟩, ⟨.or, [34, 41]⟩, ⟨.or, [36, 42]⟩], 43⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_19937_aux

open PEqualNP.Outside.L_meta_19937_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_19937 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
