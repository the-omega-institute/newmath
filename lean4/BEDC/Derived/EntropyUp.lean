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
    (distribution integral logWeight distributionTransport integralTransport logTransport ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory logWeight ∧
    hsame distributionTransport distribution ∧ hsame integralTransport integral ∧
      hsame logTransport logWeight ∧ Cont distribution integral ledger ∧
        Cont ledger logWeight endpoint ∧ PkgSig bundle endpoint pkg

theorem EntropyBHistMeasureSourceSurface_namecert_obligation_surface [AskSetup] [PackageSetup]
    {distribution integral logWeight distributionTransport integralTransport logTransport ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EntropyBHistMeasureSourceSurface distribution integral logWeight distributionTransport
        integralTransport logTransport ledger endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) (fun row : BHist => hsame row endpoint)
          hsame ∧
        UnaryHistory distribution ∧ UnaryHistory integral ∧ UnaryHistory logWeight ∧
          hsame distributionTransport distribution ∧ hsame integralTransport integral ∧
            hsame logTransport logWeight ∧ Cont distribution integral ledger ∧
              Cont ledger logWeight endpoint ∧ PkgSig bundle endpoint pkg := by
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
