import BEDC.Derived.RealityConstrainedFinalSynthesisLedgerUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedFinalSynthesisLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedFinalSynthesisLedger_carrier_namecert_surface
    [AskSetup] [PackageSetup]
    {x : TasteGate.RealityConstrainedFinalSynthesisLedgerUp}
    {truth truthCert methodology failure boundary observer synthesis transport replay provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    x =
        TasteGate.RealityConstrainedFinalSynthesisLedgerUp.mk truth truthCert methodology failure
          boundary observer synthesis transport replay provenance name →
      Cont replay name endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist => hsame row endpoint)
              (fun row : BHist => hsame row replay ∨ hsame row name ∨ hsame row endpoint)
              (fun row : BHist =>
                hsame row endpoint ∧ Cont replay name endpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            TasteGate.realityConstrainedFinalSynthesisLedgerEncodeBHist BHist.Empty =
              ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrierShape replayRoute endpointPkg
  cases carrierShape
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row replay ∨ hsame row name ∨ hsame row endpoint)
          (fun row : BHist =>
            hsame row endpoint ∧ Cont replay name endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source)
    ledger_sound := by
      intro _row source
      exact ⟨source, replayRoute, endpointPkg⟩
  }
  exact ⟨cert, rfl⟩

end BEDC.Derived.RealityConstrainedFinalSynthesisLedgerUp
