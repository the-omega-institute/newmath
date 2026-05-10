import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KoszulDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KoszulDualityExtCarrier
    (derivedRow tensorRow extClassifier varianceLedger endpoint : BHist) : Prop :=
  UnaryHistory derivedRow ∧ UnaryHistory tensorRow ∧ UnaryHistory varianceLedger ∧
    Cont derivedRow tensorRow extClassifier ∧ Cont extClassifier varianceLedger endpoint

theorem KoszulDualityDerivedTensorLedger_exactness
    {derivedRow tensorRow extClassifier varianceLedger endpoint : BHist} :
    KoszulDualityExtCarrier derivedRow tensorRow extClassifier varianceLedger endpoint ->
      UnaryHistory extClassifier ∧ UnaryHistory endpoint ∧
        hsame extClassifier (append derivedRow tensorRow) ∧
          hsame endpoint (append extClassifier varianceLedger) := by
  intro carrier
  have derivedUnary : UnaryHistory derivedRow := carrier.left
  have tensorUnary : UnaryHistory tensorRow := carrier.right.left
  have varianceUnary : UnaryHistory varianceLedger := carrier.right.right.left
  have extRow : Cont derivedRow tensorRow extClassifier := carrier.right.right.right.left
  have endpointRow : Cont extClassifier varianceLedger endpoint := carrier.right.right.right.right
  have extUnary : UnaryHistory extClassifier :=
    unary_cont_closed derivedUnary tensorUnary extRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed extUnary varianceUnary endpointRow
  exact ⟨extUnary, endpointUnary, extRow, endpointRow⟩

def KoszulDualityBHistExtCarrier [AskSetup] [PackageSetup]
    (derived tensor variance ext dual provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derived ∧ UnaryHistory tensor ∧ UnaryHistory variance ∧
    Cont derived tensor ext ∧ Cont ext variance dual ∧ Cont derived dual provenance ∧
      PkgSig bundle provenance pkg

theorem KoszulDualityBHistExtCarrier_ext_classifier_stability [AskSetup] [PackageSetup]
    {derived tensor variance ext dual provenance derived' tensor' variance' ext' dual'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KoszulDualityBHistExtCarrier derived tensor variance ext dual provenance bundle pkg ->
      hsame derived derived' -> hsame tensor tensor' -> hsame variance variance' ->
        Cont derived' tensor' ext' -> Cont ext' variance' dual' ->
          Cont derived' dual' provenance' -> PkgSig bundle provenance' pkg ->
            KoszulDualityBHistExtCarrier derived' tensor' variance' ext' dual' provenance'
                bundle pkg ∧
              hsame ext ext' ∧ hsame dual dual' ∧ hsame provenance provenance' := by
  intro carrier sameDerived sameTensor sameVariance extRow' dualRow' provenanceRow' pkgSig'
  have derivedUnary' : UnaryHistory derived' :=
    unary_transport carrier.left sameDerived
  have tensorUnary' : UnaryHistory tensor' :=
    unary_transport carrier.right.left sameTensor
  have varianceUnary' : UnaryHistory variance' :=
    unary_transport carrier.right.right.left sameVariance
  have sameExt : hsame ext ext' :=
    cont_respects_hsame sameDerived sameTensor carrier.right.right.right.left extRow'
  have sameDual : hsame dual dual' :=
    cont_respects_hsame sameExt sameVariance carrier.right.right.right.right.left dualRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameDerived sameDual carrier.right.right.right.right.right.left
      provenanceRow'
  exact
    ⟨⟨derivedUnary', tensorUnary', varianceUnary', extRow', dualRow', provenanceRow',
        pkgSig'⟩,
      sameExt, sameDual, sameProvenance⟩

end BEDC.Derived.KoszulDualityUp
