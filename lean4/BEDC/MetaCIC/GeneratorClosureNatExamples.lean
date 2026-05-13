import BEDC.MetaCIC.GeneratorClosure

namespace BEDC.MetaCIC.NatExamples

example (k : Nat) :
    GeneratorClosureClassifier Nat
      (fun m n => n = m + 1)
      (fun n => n ≥ k) :=
  { closure := by
      intro m n hgen hge
      rw [hgen]
      exact Nat.le_succ_of_le hge }

example :
    GeneratorClosureClassifier Nat
      (fun m n => m = n)
      (fun n => n = n) :=
  GeneratorClosureClassifier.refl (fun n => n = n)

end BEDC.MetaCIC.NatExamples
