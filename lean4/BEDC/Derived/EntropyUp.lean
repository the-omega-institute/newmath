import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EntropyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EntropyBHistMeasureSourceSurface [AskSetup] [PackageSetup]
    (distribution integral logWeight transport provenance observationLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory logWeight ∧
    UnaryHistory provenance ∧ Cont distribution integral observationLedger ∧
      Cont observationLedger logWeight endpoint ∧ Cont endpoint provenance transport ∧
        PkgSig bundle transport pkg

theorem EntropyBHistMeasureSourceSurface_namecert_obligation_surface [AskSetup] [PackageSetup]
    {distribution integral logWeight transport provenance observationLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntropyBHistMeasureSourceSurface distribution integral logWeight transport provenance
        observationLedger endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory logWeight ∧
          UnaryHistory provenance ∧ Cont distribution integral observationLedger ∧
            Cont observationLedger logWeight endpoint ∧ Cont endpoint provenance transport ∧
              PkgSig bundle transport pkg := by
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

theorem EntropyBHistMeasureSourceSurface_distribution_integral_boundary [AskSetup]
    [PackageSetup]
    {distribution integral logWeight transport provenance observationLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntropyBHistMeasureSourceSurface distribution integral logWeight transport provenance
        observationLedger endpoint bundle pkg ->
      UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory observationLedger ∧
        hsame observationLedger (append distribution integral) ∧ UnaryHistory endpoint ∧
          hsame endpoint (append observationLedger logWeight) ∧
            hsame transport (append endpoint provenance) ∧ PkgSig bundle transport pkg := by
  intro surface
  have distributionUnary : UnaryHistory distribution :=
    surface.left
  have integralUnary : UnaryHistory integral :=
    surface.right.left
  have logWeightUnary : UnaryHistory logWeight :=
    surface.right.right.left
  have observationLedgerRow : Cont distribution integral observationLedger :=
    surface.right.right.right.right.left
  have endpointRow : Cont observationLedger logWeight endpoint :=
    surface.right.right.right.right.right.left
  have transportRow : Cont endpoint provenance transport :=
    surface.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle transport pkg :=
    surface.right.right.right.right.right.right.right
  have observationLedgerUnary : UnaryHistory observationLedger :=
    unary_cont_closed distributionUnary integralUnary observationLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed observationLedgerUnary logWeightUnary endpointRow
  exact And.intro distributionUnary
    (And.intro integralUnary
      (And.intro observationLedgerUnary
        (And.intro observationLedgerRow
          (And.intro endpointUnary
            (And.intro endpointRow
              (And.intro transportRow pkgSig))))))

def EntropySourceSurface [AskSetup] [PackageSetup]
    (distribution integral logWeight distributionTransport integralTransport logTransport
      observationLedger sourceLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory logWeight ∧
    hsame distributionTransport distribution ∧ hsame integralTransport integral ∧
      hsame logTransport logWeight ∧ Cont distribution integral observationLedger ∧
        Cont observationLedger logWeight sourceLedger ∧
          Cont sourceLedger logTransport endpoint ∧ PkgSig bundle endpoint pkg

theorem EntropySourceSurface_namecert_obligation_surface [AskSetup] [PackageSetup]
    {distribution integral logWeight distributionTransport integralTransport logTransport
      observationLedger sourceLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntropySourceSurface distribution integral logWeight distributionTransport integralTransport
        logTransport observationLedger sourceLedger endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row logWeight)
          (fun row : BHist => hsame row logWeight)
          (fun row : BHist => hsame row logWeight) hsame ∧
        UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory logWeight ∧
          hsame distributionTransport distribution ∧ hsame integralTransport integral ∧
            hsame logTransport logWeight ∧ Cont distribution integral observationLedger ∧
              Cont observationLedger logWeight sourceLedger ∧
                Cont sourceLedger logTransport endpoint ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have cert :
      SemanticNameCert (fun row : BHist => hsame row logWeight)
          (fun row : BHist => hsame row logWeight)
          (fun row : BHist => hsame row logWeight) hsame := {
    core := {
      carrier_inhabited := Exists.intro logWeight (hsame_refl logWeight)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
     (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left
            (And.intro surface.right.right.right.right.left
              (And.intro surface.right.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.right.left
                  (And.intro surface.right.right.right.right.right.right.right.left
                    (And.intro surface.right.right.right.right.right.right.right.right.left
                      surface.right.right.right.right.right.right.right.right.right)))))))))

end BEDC.Derived.EntropyUp
