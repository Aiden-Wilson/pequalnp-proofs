import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19386

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [16, 9]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [4, 18]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [20, 21]⟩], 22⟩

theorem monotone : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19386

theorem PEqualNP.Outside.L_meta_19386 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3320506 : ℕ).testBit (5 * u.val + v.val)) 15 := by
  exact ⟨PEqualNP.Outside.L_meta_19386.witness,
    PEqualNP.Outside.L_meta_19386.monotone, by decide, by decide +kernel⟩
