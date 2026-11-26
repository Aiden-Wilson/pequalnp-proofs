import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19392

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [4, 9]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [0, 12]⟩,
    ⟨.and, [10, 13]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [3, 15]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [2, 17]⟩,
    ⟨.or, [0, 18]⟩,
    ⟨.and, [16, 19]⟩,
    ⟨.or, [14, 20]⟩], 21⟩

theorem monotone : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19392

theorem PEqualNP.Outside.L_meta_19392 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3320506 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_19392.witness,
    PEqualNP.Outside.L_meta_19392.monotone, by decide, by decide +kernel⟩
