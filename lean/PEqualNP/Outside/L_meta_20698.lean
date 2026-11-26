import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20698_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [10, 16]⟩], 17⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20698_aux

open PEqualNP.Outside.L_meta_20698_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20698 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16235552 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
