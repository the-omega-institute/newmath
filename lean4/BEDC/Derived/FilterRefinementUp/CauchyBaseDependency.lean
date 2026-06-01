import BEDC.Derived.FilterRefinementUp.CompletionRoute

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterRefinementCarrier_cauchy_base_dependency [AskSetup] [PackageSetup]
    {source target cofinal reverse transport replay provenance localName cauchyBase refinedRead
      sourceRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterRefinementCarrier source target cofinal reverse transport replay provenance localName
        bundle pkg →
      UnaryHistory cauchyBase →
        Cont cauchyBase target refinedRead →
          Cont refinedRead cofinal sourceRead →
            Cont sourceRead source completionRead →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cauchyBase ∨ hsame row target ∨ hsame row cofinal ∨
                        hsame row source ∨ hsame row refinedRead ∨ hsame row sourceRead ∨
                          hsame row completionRead)
                    (fun row : BHist =>
                      hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                    hsame ∧
                  UnaryHistory refinedRead ∧ UnaryHistory sourceRead ∧
                    UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier cauchyBaseUnary cauchyTargetRefined refinedCofinalSource
    sourceSourceCompletion completionPkg
  obtain ⟨sourceUnary, targetUnary, cofinalUnary, _reverseUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _targetCofinalSource,
    _sourceReverseReplay, _transportReplayLocalName, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed cauchyBaseUnary targetUnary cauchyTargetRefined
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed refinedUnary cofinalUnary refinedCofinalSource
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sourceReadUnary sourceUnary sourceSourceCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cauchyBase ∨ hsame row target ∨ hsame row cofinal ∨
              hsame row source ∨ hsame row refinedRead ∨ hsame row sourceRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, completionPkg⟩
  }
  exact ⟨cert, refinedUnary, sourceReadUnary, completionUnary⟩

end BEDC.Derived.FilterRefinementUp
