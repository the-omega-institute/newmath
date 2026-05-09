import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EntanglementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EntanglementBHistSourceSurface [AskSetup] [PackageSetup]
    (quantum factorLeft factorRight endpoint obstruction stateTransport factorTransport provenance
      ledger packageEndpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory quantum ∧ UnaryHistory factorLeft ∧ UnaryHistory factorRight ∧
    UnaryHistory obstruction ∧ hsame stateTransport quantum ∧
      hsame factorTransport (append factorLeft factorRight) ∧
        Cont factorLeft factorRight endpoint ∧ Cont endpoint obstruction ledger ∧
          Cont ledger provenance packageEndpoint ∧ PkgSig bundle packageEndpoint pkg

theorem EntanglementBHistSourceSurface_namecert_obligation_surface [AskSetup] [PackageSetup]
    {quantum factorLeft factorRight endpoint obstruction stateTransport factorTransport provenance
      ledger packageEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntanglementBHistSourceSurface quantum factorLeft factorRight endpoint obstruction
        stateTransport factorTransport provenance ledger packageEndpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory quantum ∧ UnaryHistory factorLeft ∧ UnaryHistory factorRight ∧
          UnaryHistory obstruction ∧ hsame stateTransport quantum ∧
            hsame factorTransport (append factorLeft factorRight) ∧
              Cont factorLeft factorRight endpoint ∧ Cont endpoint obstruction ledger ∧
                Cont ledger provenance packageEndpoint ∧ PkgSig bundle packageEndpoint pkg := by
  intro surface
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }
  exact And.intro cert surface

theorem EntanglementBHistSourceSurface_factor_boundary [AskSetup] [PackageSetup]
    {quantum factorLeft factorRight endpoint obstruction stateTransport factorTransport provenance
      ledger packageEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntanglementBHistSourceSurface quantum factorLeft factorRight endpoint obstruction
        stateTransport factorTransport provenance ledger packageEndpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory factorLeft ∧ UnaryHistory factorRight ∧ UnaryHistory endpoint ∧
          UnaryHistory obstruction ∧ Cont factorLeft factorRight endpoint ∧
            Cont endpoint obstruction ledger ∧ Cont ledger provenance packageEndpoint ∧
              PkgSig bundle packageEndpoint pkg := by
  intro surface
  have factorLeftUnary : UnaryHistory factorLeft :=
    surface.right.left
  have factorRightUnary : UnaryHistory factorRight :=
    surface.right.right.left
  have obstructionUnary : UnaryHistory obstruction :=
    surface.right.right.right.left
  have factorBoundary : Cont factorLeft factorRight endpoint :=
    surface.right.right.right.right.right.right.left
  have obstructionBoundary : Cont endpoint obstruction ledger :=
    surface.right.right.right.right.right.right.right.left
  have packageBoundary : Cont ledger provenance packageEndpoint :=
    surface.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle packageEndpoint pkg :=
    surface.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed factorLeftUnary factorRightUnary factorBoundary
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row carrier
      exact carrier
    ledger_sound := by
      intro _row carrier
      exact carrier
  }
  exact And.intro cert
    (And.intro factorLeftUnary
      (And.intro factorRightUnary
        (And.intro endpointUnary
          (And.intro obstructionUnary
            (And.intro factorBoundary
              (And.intro obstructionBoundary
                (And.intro packageBoundary pkgSig)))))))

def EntanglementSourceSurface [AskSetup] [PackageSetup]
    (quantumState leftFactor rightFactor endpoint obstruction stateTransport leftTransport
      rightTransport provenance factorLedger endpointLedger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory quantumState ∧ UnaryHistory leftFactor ∧ UnaryHistory rightFactor ∧
    UnaryHistory endpoint ∧ UnaryHistory obstruction ∧ UnaryHistory provenance ∧
      hsame stateTransport endpoint ∧ hsame leftTransport leftFactor ∧
        hsame rightTransport rightFactor ∧ Cont leftFactor rightFactor factorLedger ∧
          Cont quantumState obstruction endpointLedger ∧
            Cont factorLedger endpointLedger endpoint ∧ PkgSig bundle endpoint pkg

theorem EntanglementSourceSurface_factor_boundary [AskSetup] [PackageSetup]
    {quantumState leftFactor rightFactor endpoint obstruction stateTransport leftTransport
      rightTransport provenance factorLedger endpointLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntanglementSourceSurface quantumState leftFactor rightFactor endpoint obstruction
        stateTransport leftTransport rightTransport provenance factorLedger endpointLedger
        bundle pkg ->
      UnaryHistory leftFactor ∧ UnaryHistory rightFactor ∧ UnaryHistory obstruction ∧
        hsame stateTransport endpoint ∧ hsame leftTransport leftFactor ∧
          hsame rightTransport rightFactor ∧ Cont leftFactor rightFactor factorLedger ∧
            Cont quantumState obstruction endpointLedger ∧
              Cont factorLedger endpointLedger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have leftUnary : UnaryHistory leftFactor :=
    surface.right.left
  have rightUnary : UnaryHistory rightFactor :=
    surface.right.right.left
  have obstructionUnary : UnaryHistory obstruction :=
    surface.right.right.right.right.left
  have stateTransportEndpoint : hsame stateTransport endpoint :=
    surface.right.right.right.right.right.right.left
  have leftTransportFactor : hsame leftTransport leftFactor :=
    surface.right.right.right.right.right.right.right.left
  have rightTransportFactor : hsame rightTransport rightFactor :=
    surface.right.right.right.right.right.right.right.right.left
  have factorLedgerRow : Cont leftFactor rightFactor factorLedger :=
    surface.right.right.right.right.right.right.right.right.right.left
  have endpointLedgerRow : Cont quantumState obstruction endpointLedger :=
    surface.right.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont factorLedger endpointLedger endpoint :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro obstructionUnary
        (And.intro stateTransportEndpoint
          (And.intro leftTransportFactor
            (And.intro rightTransportFactor
              (And.intro factorLedgerRow
                (And.intro endpointLedgerRow
                (And.intro endpointRow pkgSig))))))))

theorem EntanglementSourceFactorBoundary_cont_ledger [AskSetup] [PackageSetup]
    {state factorLeft factorRight endpoint obstruction ledger provenance endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory state ->
      UnaryHistory factorLeft ->
        UnaryHistory factorRight ->
          UnaryHistory endpoint ->
            UnaryHistory obstruction ->
              UnaryHistory provenance ->
                Cont endpoint obstruction ledger ->
                  Cont provenance ledger endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      UnaryHistory factorLeft ∧ UnaryHistory factorRight ∧
                        UnaryHistory endpoint ∧ UnaryHistory obstruction ∧
                          UnaryHistory ledger ∧ hsame ledger (append endpoint obstruction) ∧
                            UnaryHistory endpoint' ∧ hsame endpoint' (append provenance ledger) ∧
                              PkgSig bundle endpoint' pkg := by
  intro _stateUnary factorLeftUnary factorRightUnary endpointUnary obstructionUnary
    provenanceUnary endpointObstructionLedger provenanceLedgerEndpoint pkgSig
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointUnary obstructionUnary endpointObstructionLedger
  have endpointPrimeUnary : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary ledgerUnary provenanceLedgerEndpoint
  exact And.intro factorLeftUnary
    (And.intro factorRightUnary
      (And.intro endpointUnary
        (And.intro obstructionUnary
          (And.intro ledgerUnary
            (And.intro endpointObstructionLedger
              (And.intro endpointPrimeUnary
                (And.intro provenanceLedgerEndpoint pkgSig)))))))

end BEDC.Derived.EntanglementUp
