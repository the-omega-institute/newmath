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

end BEDC.Derived.RingUp
