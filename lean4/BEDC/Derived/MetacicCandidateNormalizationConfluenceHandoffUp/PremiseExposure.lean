import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffPremiseExposure
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName premiseRead residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint
        frontier confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont candidate frontier premiseRead →
        Cont premiseRead confluence residualRead →
          PkgSig bundle residualRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
                    hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                      hsame row blocked ∨ hsame row transport ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row localName ∨
                          hsame row premiseRead ∨ hsame row residualRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont candidate frontier premiseRead ∧
                    Cont premiseRead confluence residualRead ∧
                      PkgSig bundle residualRead pkg)
                hsame ∧
              UnaryHistory premiseRead ∧ UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier candidateFrontierRoute premiseConfluenceRoute residualPkg
  have candidateUnary : UnaryHistory candidate := carrier.right.left
  have frontierUnary : UnaryHistory frontier := carrier.right.right.right.left
  have confluenceUnary : UnaryHistory confluence := carrier.right.right.right.right.left
  have premiseReadUnary : UnaryHistory premiseRead :=
    unary_cont_closed candidateUnary frontierUnary candidateFrontierRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed premiseReadUnary confluenceUnary premiseConfluenceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
              hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                hsame row blocked ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row premiseRead ∨
                    hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate frontier premiseRead ∧
              Cont premiseRead confluence residualRead ∧ PkgSig bundle residualRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead ⟨hsame_refl residualRead, residualReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, candidateFrontierRoute, premiseConfluenceRoute, residualPkg⟩
  }
  exact ⟨cert, premiseReadUnary, residualReadUnary⟩

end BEDC.Derived
