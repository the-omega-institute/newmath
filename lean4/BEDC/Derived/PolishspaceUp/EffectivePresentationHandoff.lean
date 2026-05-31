import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceEffectivePresentationHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream regseq ledger transport replay provenance localName
      presentationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier metric complete separable stream regseq
        ledger transport replay provenance localName bundle pkg →
      Cont separable stream presentationRead →
        PkgSig bundle presentationRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row presentationRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row ledger ∨ hsame row presentationRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle presentationRead pkg ∧
                  Cont separable stream presentationRead)
              hsame ∧
            UnaryHistory presentationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier separableStreamPresentation presentationPkg
  obtain ⟨metricUnary, _completeUnary, separableUnary, streamUnary, regseqUnary,
    ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamRegseq, _transportReplayProvenance,
    _carrierPkg⟩ := carrier
  have presentationUnary : UnaryHistory presentationRead :=
    unary_cont_closed separableUnary streamUnary separableStreamPresentation
  have sourcePresentation :
      (fun row : BHist => hsame row presentationRead ∧ UnaryHistory row) presentationRead :=
    ⟨hsame_refl presentationRead, presentationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row presentationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row ledger ∨ hsame row presentationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle presentationRead pkg ∧
              Cont separable stream presentationRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro presentationRead sourcePresentation
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
      exact ⟨source.right, presentationPkg, separableStreamPresentation⟩
  }
  exact ⟨cert, presentationUnary⟩

end BEDC.Derived.PolishspaceUp
