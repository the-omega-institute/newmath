import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RingSingletonClassifier_append_comm {h k : BHist} :
    RingSingletonCarrier h -> RingSingletonCarrier k ->
      RingSingletonClassifier (append h k) (append k h) := by
  intro carrierH carrierK
  have leftCarrier : RingSingletonCarrier (append h k) :=
    append_eq_empty_iff.mpr (And.intro carrierH carrierK)
  have rightCarrier : RingSingletonCarrier (append k h) :=
    append_eq_empty_iff.mpr (And.intro carrierK carrierH)
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem RingSingletonClassifier_append_assoc_carrier_iff {a b c : BHist} :
    RingSingletonClassifier (append (append a b) c) (append a (append b c)) <->
      RingSingletonCarrier a ∧ RingSingletonCarrier b ∧ RingSingletonCarrier c := by
  constructor
  · intro classified
    have leftOuter := append_eq_empty_iff.mp classified.left
    have leftInner := append_eq_empty_iff.mp leftOuter.left
    exact And.intro leftInner.left (And.intro leftInner.right leftOuter.right)
  · intro carriers
    have leftInner : RingSingletonCarrier (append a b) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left)
    have leftCarrier : RingSingletonCarrier (append (append a b) c) :=
      append_eq_empty_iff.mpr (And.intro leftInner carriers.right.right)
    have rightInner : RingSingletonCarrier (append b c) :=
      append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right)
    have rightCarrier : RingSingletonCarrier (append a (append b c)) :=
      append_eq_empty_iff.mpr (And.intro carriers.left rightInner)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.RingUp
