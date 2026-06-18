import BEDC.Derived.AbGroupUp
import BEDC.Derived.AbGroupUp.TasteGate

namespace BEDC.Derived.AbGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem AbgroupForgetsGroupCertificate :
    SemanticNameCert BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonClassifier ∧
      (forall {h k : BHist}, BEDC.Derived.GroupUp.GroupSingletonCarrier h ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier k ->
          BEDC.Derived.GroupUp.GroupSingletonCarrier (append h k)) ∧
      (forall {h : BHist}, BEDC.Derived.GroupUp.GroupSingletonCarrier h ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier BHist.Empty) ∧
      (forall x : AbGroupUp,
        exists carrier operation identity inverse commutativity classifier provenance endpoint :
          BHist,
          x = AbGroupUp.mk carrier operation identity inverse commutativity classifier provenance
              endpoint ∧
            abGroupFields x =
              [carrier, operation, identity, inverse, commutativity, classifier, provenance,
                endpoint]) := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame
  have laws := BEDC.Derived.GroupUp.GroupSingletonHistory_laws
  have emptyCarrier : BEDC.Derived.GroupUp.GroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  constructor
  · exact laws.left
  · constructor
    · intro h k carrierH carrierK
      exact laws.right.left carrierH carrierK
    · constructor
      · intro _h _carrierH
        exact emptyCarrier
      · intro x
        cases x with
        | mk carrier operation identity inverse commutativity classifier provenance endpoint =>
            exact
              ⟨carrier, operation, identity, inverse, commutativity, classifier, provenance,
                endpoint, rfl, rfl⟩

end BEDC.Derived.AbGroupUp
