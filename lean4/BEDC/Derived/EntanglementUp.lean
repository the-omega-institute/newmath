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
    (quantumState leftFactor rightFactor obstruction stateTransport leftTransport rightTransport
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory quantumState ∧ UnaryHistory leftFactor ∧ UnaryHistory rightFactor ∧
    UnaryHistory obstruction ∧ hsame stateTransport quantumState ∧
      hsame leftTransport leftFactor ∧ hsame rightTransport rightFactor ∧
        Cont quantumState obstruction provenance ∧ Cont leftFactor rightFactor endpoint ∧
          PkgSig bundle endpoint pkg

theorem EntanglementBHistSourceSurface_namecert_obligation_surface [AskSetup] [PackageSetup]
    {quantumState leftFactor rightFactor obstruction stateTransport leftTransport rightTransport
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntanglementBHistSourceSurface quantumState leftFactor rightFactor obstruction stateTransport
        leftTransport rightTransport provenance endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory quantumState ∧ UnaryHistory leftFactor ∧ UnaryHistory rightFactor ∧
          UnaryHistory obstruction ∧ hsame stateTransport quantumState ∧
            hsame leftTransport leftFactor ∧ hsame rightTransport rightFactor ∧
              Cont quantumState obstruction provenance ∧ Cont leftFactor rightFactor endpoint ∧
                PkgSig bundle endpoint pkg := by
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

end BEDC.Derived.EntanglementUp
