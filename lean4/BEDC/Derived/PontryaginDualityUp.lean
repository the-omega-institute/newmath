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

theorem PontryaginDualityCharacterCarrier_obligation [AskSetup] [PackageSetup]
    {topGroupRow abGroupRow circleTarget characterRows productRows inverseRows sourceLedger
      characterLedger operationLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory topGroupRow ->
      UnaryHistory abGroupRow ->
        UnaryHistory circleTarget ->
          UnaryHistory characterRows ->
            UnaryHistory productRows ->
              UnaryHistory inverseRows ->
                Cont topGroupRow abGroupRow sourceLedger ->
                  Cont circleTarget characterRows characterLedger ->
                    Cont productRows inverseRows operationLedger ->
                      Cont sourceLedger characterLedger provenance ->
                        Cont provenance operationLedger endpoint ->
                          PkgSig bundle endpoint pkg ->
                            UnaryHistory sourceLedger ∧ UnaryHistory characterLedger ∧
                              UnaryHistory operationLedger ∧ UnaryHistory provenance ∧
                                UnaryHistory endpoint ∧
                                  hsame sourceLedger (append topGroupRow abGroupRow) ∧
                                    hsame characterLedger (append circleTarget characterRows) ∧
                                      hsame operationLedger (append productRows inverseRows) ∧
                                        hsame provenance (append sourceLedger characterLedger) ∧
                                          hsame endpoint (append provenance operationLedger) ∧
                                            PkgSig bundle endpoint pkg := by
  intro topGroupUnary abGroupUnary circleUnary characterRowsUnary productRowsUnary
    inverseRowsUnary sourceRow characterRow operationRow provenanceRow endpointRow endpointPkg
  have sourceUnary : UnaryHistory sourceLedger :=
    unary_cont_closed topGroupUnary abGroupUnary sourceRow
  have characterUnary : UnaryHistory characterLedger :=
    unary_cont_closed circleUnary characterRowsUnary characterRow
  have operationUnary : UnaryHistory operationLedger :=
    unary_cont_closed productRowsUnary inverseRowsUnary operationRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed sourceUnary characterUnary provenanceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary operationUnary endpointRow
  exact
    ⟨sourceUnary,
      characterUnary,
      operationUnary,
      provenanceUnary,
      endpointUnary,
      sourceRow,
      characterRow,
      operationRow,
      provenanceRow,
      endpointRow,
      endpointPkg⟩

end BEDC.Derived.PontryaginDualityUp
