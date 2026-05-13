import BEDC.MetaCIC.GeneratorClosure

namespace BEDC.MetaCIC.Examples

example (d : Idx) :
    GeneratorClosureClassifier Term
      (fun t1 t2 : Term => t1 = t2)
      (ClosedAt d) :=
  GeneratorClosureClassifier.refl (ClosedAt d)

example (d : Idx) :
    GeneratorClosureClassifier Term
      (fun t1 t3 : Term =>
        ∃ t2, t2 = shift d 1 t1 ∧ ∃ v, t3 = substitute d v t2)
      (ClosedAt d) :=
  GeneratorClosureClassifier.comp
    (closed_under_shift_classifier d)
    (closed_under_substitute_classifier d)

example (d : Idx) :
    GeneratorClosureClassifier Term
      (fun t1 t2 : Term =>
        t2 = shift d 1 t1 ∨ ∃ v, t2 = substitute d v t1)
      (ClosedAt d) :=
  GeneratorClosureClassifier.union
    (closed_under_shift_classifier d)
    (closed_under_substitute_classifier d)

/-- Cross-carrier example: combine the Term-side closed-term substitute classifier
    with the Nat-side succ-preserves-ge-k classifier via `.product`. -/
example (d : Idx) (k : Nat) :
    GeneratorClosureClassifier (Term × Nat)
      (fun p1 p2 =>
        (∃ v, p2.1 = substitute d v p1.1) ∧ p2.2 = p1.2 + 1)
      (fun p => ClosedAt d p.1 ∧ p.2 ≥ k) :=
  GeneratorClosureClassifier.product
    (closed_under_substitute_classifier d)
    ({ closure := by
        intro m n hgen hge
        rw [hgen]
        exact Nat.le_succ_of_le hge } :
      GeneratorClosureClassifier Nat
        (fun m n => n = m + 1)
        (fun n => n ≥ k))

end BEDC.MetaCIC.Examples
