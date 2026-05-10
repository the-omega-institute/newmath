import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PontryaginDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PontryaginDualityCharacterCarrier [AskSetup] [PackageSetup]
    (topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory topSource ∧ UnaryHistory abSource ∧ UnaryHistory circleTarget ∧
    UnaryHistory character ∧ UnaryHistory productRow ∧ UnaryHistory inverseRow ∧
      Cont topSource abSource sourceLedger ∧ Cont circleTarget character characterLedger ∧
        Cont sourceLedger characterLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem PontryaginDualityCharacterCarrier_stability [AskSetup] [PackageSetup]
    {topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint topSource' abSource' circleTarget' character' productRow'
      inverseRow' sourceLedger' characterLedger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PontryaginDualityCharacterCarrier topSource abSource circleTarget character productRow
        inverseRow sourceLedger characterLedger endpoint bundle pkg ->
      hsame topSource topSource' ->
        hsame abSource abSource' ->
          hsame circleTarget circleTarget' ->
            hsame character character' ->
              hsame productRow productRow' ->
                hsame inverseRow inverseRow' ->
                  Cont topSource' abSource' sourceLedger' ->
                    Cont circleTarget' character' characterLedger' ->
                      Cont sourceLedger' characterLedger' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          PontryaginDualityCharacterCarrier topSource' abSource' circleTarget'
                              character' productRow' inverseRow' sourceLedger'
                              characterLedger' endpoint' bundle pkg ∧
                            hsame sourceLedger sourceLedger' ∧
                              hsame characterLedger characterLedger' ∧
                                hsame endpoint endpoint' := by
  intro carrier sameTopSource sameAbSource sameCircleTarget sameCharacter sameProductRow
    sameInverseRow sourceLedgerRow' characterLedgerRow' endpointRow' pkgSig'
  have topSourceUnary' : UnaryHistory topSource' :=
    unary_transport carrier.left sameTopSource
  have abSourceUnary' : UnaryHistory abSource' :=
    unary_transport carrier.right.left sameAbSource
  have circleTargetUnary' : UnaryHistory circleTarget' :=
    unary_transport carrier.right.right.left sameCircleTarget
  have characterUnary' : UnaryHistory character' :=
    unary_transport carrier.right.right.right.left sameCharacter
  have productRowUnary' : UnaryHistory productRow' :=
    unary_transport carrier.right.right.right.right.left sameProductRow
  have inverseRowUnary' : UnaryHistory inverseRow' :=
    unary_transport carrier.right.right.right.right.right.left sameInverseRow
  have sameSourceLedger : hsame sourceLedger sourceLedger' :=
    cont_respects_hsame sameTopSource sameAbSource
      carrier.right.right.right.right.right.right.left sourceLedgerRow'
  have sameCharacterLedger : hsame characterLedger characterLedger' :=
    cont_respects_hsame sameCircleTarget sameCharacter
      carrier.right.right.right.right.right.right.right.left characterLedgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSourceLedger sameCharacterLedger
      carrier.right.right.right.right.right.right.right.right.left endpointRow'
  exact
    ⟨⟨topSourceUnary', abSourceUnary', circleTargetUnary', characterUnary', productRowUnary',
        inverseRowUnary', sourceLedgerRow', characterLedgerRow', endpointRow', pkgSig'⟩,
      sameSourceLedger, sameCharacterLedger, sameEndpoint⟩

theorem PontryaginDualityCharacterCarrier_source_boundary [AskSetup] [PackageSetup]
    {topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PontryaginDualityCharacterCarrier topSource abSource circleTarget character productRow
        inverseRow sourceLedger characterLedger endpoint bundle pkg ->
      UnaryHistory sourceLedger ∧ UnaryHistory characterLedger ∧ UnaryHistory endpoint ∧
        hsame sourceLedger (append topSource abSource) ∧
          hsame characterLedger (append circleTarget character) ∧
            hsame endpoint (append sourceLedger characterLedger) ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have characterLedgerUnary : UnaryHistory characterLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceLedgerUnary characterLedgerUnary
      carrier.right.right.right.right.right.right.right.right.left
  exact
    ⟨sourceLedgerUnary,
      characterLedgerUnary,
      endpointUnary,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.PontryaginDualityUp
