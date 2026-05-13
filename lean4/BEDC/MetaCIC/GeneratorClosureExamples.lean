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

end BEDC.MetaCIC.Examples
