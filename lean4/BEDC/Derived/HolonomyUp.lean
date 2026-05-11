import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HolonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HolonomyTransportCarrier [AskSetup] [PackageSetup]
    (bundle connection loop endpoint curvature ledger provenance : BHist)
    (probeBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundle ∧ UnaryHistory connection ∧ UnaryHistory loop ∧
    UnaryHistory endpoint ∧ UnaryHistory curvature ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont loop connection ledger ∧ Cont ledger curvature endpoint ∧
        PkgSig probeBundle endpoint pkg

theorem HolonomyTransportCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvature ledger provenance : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
        probeBundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
            probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
            probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
            probeBundle pkg ∧ hsame row endpoint)
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

end BEDC.Derived.HolonomyUp
