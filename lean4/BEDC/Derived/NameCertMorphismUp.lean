import BEDC.Derived.NameCertMorphismUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NameCertMorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem NameCertMorphismUp_composition_obligation
    {source _middle target graph₁ _same₁ route₁ _provenance₁ _name₁ graph₂ _same₂ route₂
      _provenance₂ _name₂
      compositeGraph compositeSame compositeRoute compositeProvenance compositeName : BHist} :
    UnaryHistory graph₁ → UnaryHistory graph₂ → UnaryHistory route₁ → UnaryHistory route₂ →
      Cont graph₁ graph₂ compositeGraph → Cont route₁ route₂ compositeRoute →
        UnaryHistory compositeGraph ∧ UnaryHistory compositeRoute ∧
          nameCertMorphismFromEventFlow
            (nameCertMorphismToEventFlow
              (NameCertMorphismUp.mk source target compositeGraph compositeSame compositeRoute
                compositeProvenance compositeName)) =
            some (NameCertMorphismUp.mk source target compositeGraph compositeSame compositeRoute
              compositeProvenance compositeName) := by
  intro graphUnary₁ graphUnary₂ routeUnary₁ routeUnary₂ graphCont routeCont
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphUnary₁ graphUnary₂ graphCont
  have compositeRouteUnary : UnaryHistory compositeRoute :=
    unary_cont_closed routeUnary₁ routeUnary₂ routeCont
  have roundTrip :
      ∀ x : NameCertMorphismUp,
        nameCertMorphismFromEventFlow (nameCertMorphismToEventFlow x) = some x :=
    NameCertMorphismTasteGate_single_carrier_alignment.right.left
  constructor
  · exact compositeGraphUnary
  · constructor
    · exact compositeRouteUnary
    · exact roundTrip
        (NameCertMorphismUp.mk source target compositeGraph compositeSame compositeRoute
          compositeProvenance compositeName)

end BEDC.Derived.NameCertMorphismUp
