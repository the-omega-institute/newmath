import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchySpeedupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def CauchySpeedupCarrier [AskSetup] [PackageSetup]
    (A J D W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont A J W ∧
    Cont W R E ∧
      hsame D D ∧
        Cont H C N ∧
          PkgSig bundle P pkg

theorem CauchySpeedupNameCertObligations [AskSetup] [PackageSetup]
    {A J D W R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySpeedupCarrier A J D W R E H C P N bundle pkg ->
      Cont A J W ->
        Cont W R E ->
          PkgSig bundle P pkg ->
            SemanticNameCert
              (fun row : BHist =>
                CauchySpeedupCarrier A J D W R E H C P N bundle pkg ∧ hsame row N)
              (fun row : BHist => Cont A J W ∧ Cont W R E ∧ hsame row N)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier sourceWindow windowSeal provenance
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrier, hsame_refl N⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨sourceWindow, windowSeal, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenance, source.right⟩
  }

end BEDC.Derived.CauchySpeedupUp
