import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralMeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpectralMeasurePacketCarrier [AskSetup] [PackageSetup]
    (hilbert observable event projection orthogonality additivity ledger endpoint : BHist)
    (probeBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory observable ∧ UnaryHistory event ∧
    UnaryHistory projection ∧ UnaryHistory orthogonality ∧ UnaryHistory additivity ∧
      UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont event projection ledger ∧
        Cont orthogonality additivity endpoint ∧ PkgSig probeBundle endpoint pkg

theorem SpectralMeasurePacketCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {hilbert observable event projection orthogonality additivity ledger endpoint : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpectralMeasurePacketCarrier hilbert observable event projection orthogonality additivity
        ledger endpoint probeBundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SpectralMeasurePacketCarrier hilbert observable event projection orthogonality
            additivity ledger endpoint probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          SpectralMeasurePacketCarrier hilbert observable event projection orthogonality
            additivity ledger endpoint probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          SpectralMeasurePacketCarrier hilbert observable event projection orthogonality
            additivity ledger endpoint probeBundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.SpectralMeasureUp
