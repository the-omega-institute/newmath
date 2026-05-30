import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompletionNonescape [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont complete stream completionRead →
        PkgSig bundle provenance pkg →
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row complete ∨ hsame row stream ∨ hsame row readback ∨
                  hsame row ledger ∨ hsame row transport ∨ hsame row route ∨
                    hsame row localName ∨ hsame row completionRead)
              (fun row : BHist =>
                hsame row completionRead ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completeStreamCompletion provenancePkgInput
  obtain ⟨_metricUnary, completeUnary, _separableUnary, streamUnary, _readbackUnary,
    _ledgerUnary, _alignmentUnary, _transportUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, _ledgerTransportRoute, _provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row complete ∨ hsame row stream ∨ hsame row readback ∨
              hsame row ledger ∨ hsame row transport ∨ hsame row route ∨
                hsame row localName ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkgInput⟩
  }
  exact ⟨cert, completionUnary⟩

end BEDC.Derived.PolishspaceUp
