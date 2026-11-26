import PEqualNP.Defs

/-!
# Counterexample to L-meta-18726

Fix the third input to false. Two gates independently compute the AND of
the first two inputs. An OR of their outputs computes the same AND.
For each copy, the other copy witnesses that its only reader can bypass it.
Dropping both copies and their reader would leave zero gates. No choice
of a wire in an empty circuit computes the AND of the two inputs.
-/

namespace TwoCopies

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def copies : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.and,[0,1]⟩, ⟨.or,[3,4]⟩],5⟩

def keep : Finset (Fin 3) := {2}
def dropCopies : Finset (Fin 3) := {0,1}

def fixedEval (x : Fin 3 → Bool) : Bool :=
  copies.eval (List.ofFn (Function.update x 2 false))

theorem noEmpty {D : Circuit} (hd : D.size = 0)
    (h : ∀ x : Fin 3 → Bool, D.eval (List.ofFn x) = fixedEval x) : False := by
  rcases D with ⟨gs,o⟩
  have nil : gs = [] := List.length_eq_zero_iff.mp hd
  subst gs
  have atOnes := h (fun _ => true)
  change ([true,true,true] : List Bool).getD o false = true at atOnes
  have ho : o < 3 := by
    by_contra! hn
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hn)] at atOnes
    contradiction
  interval_cases o
  · have hh := h ![true,false,false]
    contradiction
  · have hh := h ![false,true,false]
    contradiction
  · have hh := h ![false,false,true]
    contradiction

theorem refutation : ¬ (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K P : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → Disjoint K P → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ (∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, w < n + j.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false) → (∀ p ∈ P, n + p.val ≠ C.output ∧ ∀ k : Fin C.gates.length, n + p.val ∈ (C.gates.get k).inputs → k ∈ P ∨ (k ∈ K ∧ ((∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = c) ∨ ∃ w ∈ (C.gates.get k).inputs, w < n + k.val ∧ w ≠ n + p.val ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + k.val) false = (C.wires (List.ofFn (Function.update x v b))).getD w false))) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card + P.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b))) := by
  intro claim
  have h := claim 3 copies 2 false keep dropCopies
  have fan : FanInTwo copies := by
    intro g hg
    simp only [copies, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  have nots : ∀ g ∈ copies.gates, g.op = GateOp.not → g.inputs.length = 1 := by
    intro g hg
    simp only [copies, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  have hdis : Disjoint keep dropCopies := by decide +kernel
  specialize h fan nots ⟨fun _ => false, rfl⟩ hdis
  have ksave : ∀ j ∈ keep, ∃ w ∈ (copies.gates.get j).inputs, w < 3 + j.val ∧
      ∀ x : Fin 3 → Bool, (copies.wires (List.ofFn (Function.update x 2 false))).getD
        (3 + j.val) false = (copies.wires (List.ofFn (Function.update x 2 false))).getD w false := by
    decide +kernel
  specialize h (fun j hj => Or.inr (Or.inr (ksave j hj)))
  have preaders : ∀ p ∈ dropCopies, 3 + p.val ≠ copies.output ∧
      ∀ k : Fin 3, 3 + p.val ∈ (copies.gates.get k).inputs →
      k ∈ keep ∧ ∃ w ∈ (copies.gates.get k).inputs, w < 3 + k.val ∧ w ≠ 3 + p.val ∧
      ∀ x : Fin 3 → Bool, (copies.wires (List.ofFn (Function.update x 2 false))).getD
        (3 + k.val) false = (copies.wires (List.ofFn (Function.update x 2 false))).getD w false := by
    decide +kernel
  obtain ⟨D, _, hs, he⟩ := h (fun p hp => ⟨(preaders p hp).1, fun k hk =>
    Or.inr ⟨((preaders p hp).2 k hk).1, Or.inr ((preaders p hp).2 k hk).2⟩⟩)
  apply noEmpty (D := D) _ he
  change D.size + 1 + 2 ≤ 3 at hs
  omega

end TwoCopies
