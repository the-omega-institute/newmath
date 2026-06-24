import BEDC.Derived.UniformBoundednessUp

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessNormEnvelopeExactness [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      normEnvelopeRead rationalBudgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg ->
      Cont norm regseq normEnvelopeRead ->
        Cont normEnvelopeRead history rationalBudgetRead ->
          PkgSig bundle rationalBudgetRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row rationalBudgetRead ∧
                    UniformBoundednessPacket family pointwise baire norm regseq stream
                      transport history replay provenance nameRow bundle pkg)
                (fun row : BHist =>
                  hsame row norm ∨ hsame row regseq ∨ hsame row history ∨
                    hsame row normEnvelopeRead ∨ hsame row rationalBudgetRead)
                (fun row : BHist =>
                  hsame row rationalBudgetRead ∧ Cont norm regseq normEnvelopeRead ∧
                    Cont normEnvelopeRead history rationalBudgetRead ∧
                      PkgSig bundle rationalBudgetRead pkg)
                hsame ∧
              Cont norm regseq normEnvelopeRead ∧
                Cont normEnvelopeRead history rationalBudgetRead ∧
                  PkgSig bundle rationalBudgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro packet normEnvelopeRoute budgetRoute budgetPkg
  have sourceBudget :
      hsame rationalBudgetRead rationalBudgetRead ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact ⟨hsame_refl rationalBudgetRead, packet⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row rationalBudgetRead ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row norm ∨ hsame row regseq ∨ hsame row history ∨
              hsame row normEnvelopeRead ∨ hsame row rationalBudgetRead)
          (fun row : BHist =>
            hsame row rationalBudgetRead ∧ Cont norm regseq normEnvelopeRead ∧
              Cont normEnvelopeRead history rationalBudgetRead ∧
                PkgSig bundle rationalBudgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rationalBudgetRead sourceBudget
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, packet⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, normEnvelopeRoute, budgetRoute, budgetPkg⟩
  }
  exact ⟨cert, normEnvelopeRoute, budgetRoute, budgetPkg⟩

end BEDC.Derived.UniformBoundednessUp
