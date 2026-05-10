import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PontryaginDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem PontryaginDualityCharacterCarrier_operation_ledger_boundary [AskSetup]
    [PackageSetup]
    {topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint operationLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PontryaginDualityCharacterCarrier topSource abSource circleTarget character productRow
        inverseRow sourceLedger characterLedger endpoint bundle pkg ->
      Cont productRow inverseRow operationLedger ->
        UnaryHistory productRow ∧ UnaryHistory inverseRow ∧ UnaryHistory operationLedger ∧
          hsame operationLedger (append productRow inverseRow) ∧ PkgSig bundle endpoint pkg := by
  intro carrier operationRow
  have operationUnary : UnaryHistory operationLedger :=
    unary_cont_closed carrier.right.right.right.right.left
      carrier.right.right.right.right.right.left operationRow
  exact
    ⟨carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      operationUnary,
      operationRow,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem PontryaginDualityCharacterCarrier_dual_ledger_rows [AskSetup] [PackageSetup]
    {topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PontryaginDualityCharacterCarrier topSource abSource circleTarget character productRow
        inverseRow sourceLedger characterLedger endpoint bundle pkg ->
      UnaryHistory character ∧ UnaryHistory productRow ∧ UnaryHistory inverseRow ∧
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
    ⟨carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      sourceLedgerUnary,
      characterLedgerUnary,
      endpointUnary,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem PontryaginDualityCharacterCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PontryaginDualityCharacterCarrier topSource abSource circleTarget character productRow
        inverseRow sourceLedger characterLedger endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            PontryaginDualityCharacterCarrier topSource abSource circleTarget character
              productRow inverseRow sourceLedger characterLedger endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            PontryaginDualityCharacterCarrier topSource abSource circleTarget character
              productRow inverseRow sourceLedger characterLedger endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            PontryaginDualityCharacterCarrier topSource abSource circleTarget character
              productRow inverseRow sourceLedger characterLedger endpoint bundle pkg ∧
              hsame row endpoint)
          hsame ∧
        UnaryHistory sourceLedger ∧ UnaryHistory characterLedger ∧ UnaryHistory endpoint ∧
          Cont topSource abSource sourceLedger ∧ Cont circleTarget character characterLedger ∧
            Cont sourceLedger characterLedger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have topSourceUnary : UnaryHistory topSource := carrier.left
  have abSourceUnary : UnaryHistory abSource := carrier.right.left
  have circleTargetUnary : UnaryHistory circleTarget := carrier.right.right.left
  have characterUnary : UnaryHistory character := carrier.right.right.right.left
  have sourceLedgerRow : Cont topSource abSource sourceLedger :=
    carrier.right.right.right.right.right.right.left
  have characterLedgerRow : Cont circleTarget character characterLedger :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont sourceLedger characterLedger endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed topSourceUnary abSourceUnary sourceLedgerRow
  have characterLedgerUnary : UnaryHistory characterLedger :=
    unary_cont_closed circleTargetUnary characterUnary characterLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceLedgerUnary characterLedgerUnary endpointRow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            PontryaginDualityCharacterCarrier topSource abSource circleTarget character
              productRow inverseRow sourceLedger characterLedger endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            PontryaginDualityCharacterCarrier topSource abSource circleTarget character
              productRow inverseRow sourceLedger characterLedger endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            PontryaginDualityCharacterCarrier topSource abSource circleTarget character
              productRow inverseRow sourceLedger characterLedger endpoint bundle pkg ∧
              hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert,
      sourceLedgerUnary,
      characterLedgerUnary,
      endpointUnary,
      sourceLedgerRow,
      characterLedgerRow,
      endpointRow,
      pkgSig⟩

theorem PontryaginDualityCharacterCarrier_visible_dual_ledger_boundary [AskSetup]
    [PackageSetup]
    {topSource abSource circleTarget character productRow inverseRow sourceLedger
      characterLedger endpoint operationLedger provenance dualLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PontryaginDualityCharacterCarrier topSource abSource circleTarget character productRow
        inverseRow sourceLedger characterLedger endpoint bundle pkg ->
      Cont productRow inverseRow operationLedger ->
        Cont sourceLedger characterLedger provenance ->
          Cont provenance operationLedger dualLedger ->
            UnaryHistory operationLedger ∧ UnaryHistory provenance ∧
              UnaryHistory dualLedger ∧ hsame operationLedger (append productRow inverseRow) ∧
                hsame provenance (append sourceLedger characterLedger) ∧
                  hsame dualLedger (append provenance operationLedger) ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier operationRow provenanceRow dualLedgerRow
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have characterLedgerUnary : UnaryHistory characterLedger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have operationLedgerUnary : UnaryHistory operationLedger :=
    unary_cont_closed carrier.right.right.right.right.left
      carrier.right.right.right.right.right.left operationRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed sourceLedgerUnary characterLedgerUnary provenanceRow
  have dualLedgerUnary : UnaryHistory dualLedger :=
    unary_cont_closed provenanceUnary operationLedgerUnary dualLedgerRow
  exact
    ⟨operationLedgerUnary,
      provenanceUnary,
      dualLedgerUnary,
      operationRow,
      provenanceRow,
      dualLedgerRow,
      carrier.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.PontryaginDualityUp
