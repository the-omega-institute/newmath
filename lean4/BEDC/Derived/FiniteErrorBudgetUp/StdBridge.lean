import BEDC.Derived.FiniteErrorBudgetUp

namespace BEDC.Derived.FiniteErrorBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteErrorBudgetUp_StdBridge [AskSetup] [PackageSetup]
    {requestRow toleranceRow selectorRow tailRow budgetRow readbackRow sealRow provenanceRow
      nameRow completionRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteErrorBudgetCarrier requestRow toleranceRow selectorRow tailRow budgetRow readbackRow
        sealRow provenanceRow nameRow bundle pkg ->
      Cont sealRow provenanceRow completionRead ->
        Cont completionRead nameRow exported ->
          PkgSig bundle exported pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist =>
                Cont completionRead nameRow row ∧ Cont sealRow provenanceRow completionRead)
              (fun row : BHist =>
                PkgSig bundle row pkg ∧ hsame provenanceRow (append sealRow nameRow))
              (fun row row' : BHist => hsame row row') := by
  intro carrier completionRoute exportRoute exportPkg
  obtain ⟨_requestUnary, _toleranceUnary, _selectorUnary, _tailUnary, _budgetUnary,
    _readbackUnary, sealUnary, provenanceUnary, nameRowUnary, _requestSelectorRoute,
    _selectorBudgetRoute, _budgetSealRoute, provenanceName, _provenancePkg⟩ := carrier
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary provenanceUnary completionRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed completionReadUnary nameRowUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact ⟨cont_result_hsame_transport exportRoute (hsame_symm source.left), completionRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, provenanceName⟩
  }

end BEDC.Derived.FiniteErrorBudgetUp
