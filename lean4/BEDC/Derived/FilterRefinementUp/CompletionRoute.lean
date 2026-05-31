import BEDC.Derived.FilterRefinementUp.CauchyPreservation

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterRefinementCompletionRoute [AskSetup] [PackageSetup]
    {source target cofinal reverse transport replay provenance localName refinedRead sourceRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterRefinementCarrier source target cofinal reverse transport replay provenance localName
        bundle pkg →
      Cont target cofinal refinedRead →
        Cont refinedRead source sourceRead →
          Cont sourceRead replay completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row target ∨ hsame row cofinal ∨ hsame row source ∨
                      hsame row refinedRead ∨ hsame row sourceRead ∨ hsame row completionRead)
                  (fun row : BHist =>
                    hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory refinedRead ∧ UnaryHistory sourceRead ∧
                  UnaryHistory completionRead ∧ Cont target cofinal refinedRead ∧
                    Cont refinedRead source sourceRead ∧ Cont sourceRead replay completionRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier targetCofinalRefined refinedSourceRead sourceReplayCompletion completionPkg
  obtain ⟨sourceUnary, targetUnary, cofinalUnary, _reverseUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, _targetCofinalSource,
    _sourceReverseReplay, _transportReplayLocalName, provenancePkg, _localNamePkg⟩ :=
    carrier
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed targetUnary cofinalUnary targetCofinalRefined
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed refinedUnary sourceUnary refinedSourceRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sourceReadUnary replayUnary sourceReplayCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row cofinal ∨ hsame row source ∨
              hsame row refinedRead ∨ hsame row sourceRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, completionPkg⟩
  }
  exact
    ⟨cert, refinedUnary, sourceReadUnary, completionReadUnary, targetCofinalRefined,
      refinedSourceRead, sourceReplayCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.FilterRefinementUp
