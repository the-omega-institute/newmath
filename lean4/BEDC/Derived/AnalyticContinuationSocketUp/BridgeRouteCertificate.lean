import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_bridge_route_certificate [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      bridgeRead zetaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      Cont output branch bridgeRead →
        Cont bridgeRead transport zetaRead →
          PkgSig bundle zetaRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row leftOverlap ∨ hsame row witness ∨
                    hsame row operation ∨ hsame row output ∨ hsame row branch ∨
                      hsame row transport ∨ hsame row continuation ∨
                        hsame row provenance ∨ hsame row name ∨
                          hsame row bridgeRead ∨ hsame row zetaRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont output branch bridgeRead ∧
                    Cont bridgeRead transport zetaRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle zetaRead pkg)
                hsame ∧ UnaryHistory bridgeRead ∧ UnaryHistory zetaRead := by
  -- BEDC touchpoint anchor: AnalyticContinuationSocketCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier outputBranchRoute bridgeTransportRoute zetaPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, _branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed outputUnary branchUnary outputBranchRoute
  have zetaReadUnary : UnaryHistory zetaRead :=
    unary_cont_closed bridgeReadUnary transportUnary bridgeTransportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row leftOverlap ∨ hsame row witness ∨
              hsame row operation ∨ hsame row output ∨ hsame row branch ∨
                hsame row transport ∨ hsame row continuation ∨
                  hsame row provenance ∨ hsame row name ∨
                    hsame row bridgeRead ∨ hsame row zetaRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont output branch bridgeRead ∧
              Cont bridgeRead transport zetaRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle zetaRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro zetaRead ⟨hsame_refl zetaRead, zetaReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, outputBranchRoute, bridgeTransportRoute, provenancePkg,
          zetaPkg⟩
  }
  exact ⟨cert, bridgeReadUnary, zetaReadUnary⟩

end BEDC.Derived.AnalyticContinuationSocketUp
