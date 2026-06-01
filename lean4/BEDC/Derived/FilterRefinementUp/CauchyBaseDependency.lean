import BEDC.Derived.FilterRefinementUp.CauchyPreservation

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterRefinementCauchyBaseDependency [AskSetup] [PackageSetup]
    {source target cofinal reverse transport replay provenance localName cauchyBase
      refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterRefinementCarrier source target cofinal reverse transport replay provenance localName
        bundle pkg →
      Cont target cofinal cauchyBase →
        Cont cauchyBase replay refinedRead →
          PkgSig bundle refinedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row target ∨ hsame row cofinal ∨
                    hsame row cauchyBase ∨ hsame row refinedRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle refinedRead pkg)
                hsame ∧
              UnaryHistory cauchyBase ∧ UnaryHistory refinedRead := by
  -- BEDC touchpoint anchor: BHist FilterRefinementCarrier Cont ProbeBundle Pkg SemanticNameCert
  intro carrier cauchyRoute refinedRoute refinedPkg
  obtain ⟨_sourceUnary, targetUnary, cofinalUnary, _reverseUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, _targetCofinalSource,
    _sourceReverseReplay, _transportReplayLocalName, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have cauchyUnary : UnaryHistory cauchyBase :=
    unary_cont_closed targetUnary cofinalUnary cauchyRoute
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed cauchyUnary replayUnary refinedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row cofinal ∨
              hsame row cauchyBase ∨ hsame row refinedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle refinedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedRead ⟨hsame_refl refinedRead, refinedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, refinedPkg⟩
  }
  exact ⟨cert, cauchyUnary, refinedUnary⟩

end BEDC.Derived.FilterRefinementUp
