import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverLedgerRealization [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName coverRead ledgerRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg ->
      Cont epsilonNet cover coverRead ->
        Cont coverRead lebesgue ledgerRead ->
          Cont ledgerRead orderBound orderRead ->
            PkgSig bundle orderRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row epsilonNet ∨ hsame row cover ∨ hsame row lebesgue ∨
                      hsame row orderBound ∨ hsame row ledgerRead ∨ hsame row orderRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont coverRead lebesgue ledgerRead ∧
                      Cont ledgerRead orderBound orderRead ∧ PkgSig bundle orderRead pkg)
                  hsame ∧
                UnaryHistory coverRead ∧ UnaryHistory ledgerRead ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonCoverRead coverLebesgueLedger ledgerOrderRead orderPkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed coverReadUnary lebesgueUnary coverLebesgueLedger
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed ledgerReadUnary orderUnary ledgerOrderRead
  have sourceOrder :
      (fun row : BHist => hsame row orderRead ∧ UnaryHistory row) orderRead := by
    exact ⟨hsame_refl orderRead, orderReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilonNet ∨ hsame row cover ∨ hsame row lebesgue ∨
              hsame row orderBound ∨ hsame row ledgerRead ∨ hsame row orderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverRead lebesgue ledgerRead ∧
              Cont ledgerRead orderBound orderRead ∧ PkgSig bundle orderRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro orderRead sourceOrder
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
        exact
          Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, coverLebesgueLedger, ledgerOrderRead, orderPkg⟩
    }
  exact ⟨cert, coverReadUnary, ledgerReadUnary, orderReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
