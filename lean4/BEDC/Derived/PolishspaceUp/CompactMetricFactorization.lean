import BEDC.Derived.PolishspaceUp.RootUnblockSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompactMetricFactorization [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      compactMetricRead completionFacingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      Cont metric complete compactMetricRead →
        Cont compactMetricRead readback completionFacingRead →
          SemanticNameCert
              (fun row : BHist => hsame row completionFacingRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                  hsame row stream ∨ hsame row readback ∨ hsame row completionFacingRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory compactMetricRead ∧ UnaryHistory completionFacingRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface metricCompleteRead compactReadbackRead
  obtain ⟨metricUnary, completeUnary, _separableUnary, _streamUnary, readbackUnary,
    _ledgerUnary, _transportUnary, _localNameUnary, _metricCompleteSurface,
    _metricSeparableSurface, _ledgerTransportReplay, provenancePkg, localNamePkg⟩ := surface
  have compactMetricUnary : UnaryHistory compactMetricRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have completionFacingUnary : UnaryHistory completionFacingRead :=
    unary_cont_closed compactMetricUnary readbackUnary compactReadbackRead
  have sourceCompletion :
      (fun row : BHist => hsame row completionFacingRead ∧ UnaryHistory row)
        completionFacingRead := by
    exact ⟨hsame_refl completionFacingRead, completionFacingUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionFacingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row completionFacingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionFacingRead sourceCompletion
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, compactMetricUnary, completionFacingUnary⟩

end BEDC.Derived.PolishspaceUp
