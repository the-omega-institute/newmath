import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def ModulusOfConvergencePacket [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont precision selector modulus ∧
    Cont modulus schedule witness ∧
      Cont witness ledger provenance ∧
        Cont provenance BHist.Empty endpoint ∧
          PkgSig bundle endpoint pkg

theorem ModulusOfConvergencePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergencePacket precision selector modulus schedule witness ledger provenance
      endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            ModulusOfConvergencePacket precision selector modulus schedule witness ledger
              provenance endpoint bundle pkg)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro (hsame_refl endpoint) packet)
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    }
    pattern_sound := by
      intro _h source
      exact source.left
    ledger_sound := by
      intro _h source
      exact And.intro source.left source.right.right.right.right.right
  }

end BEDC.Derived.ModulusOfConvergenceUp
