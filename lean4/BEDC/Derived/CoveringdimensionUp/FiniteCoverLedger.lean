import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverLedger [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName ledgerRead scaleRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg ->
      Cont cover refinement ledgerRead ->
        Cont ledgerRead lebesgue scaleRead ->
          Cont scaleRead localName namedRead ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                        hsame row ledgerRead ∨ hsame row scaleRead ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont cover refinement ledgerRead ∧
                      Cont ledgerRead lebesgue scaleRead ∧
                        Cont scaleRead localName namedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory ledgerRead ∧ UnaryHistory scaleRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ledgerRoute scaleRoute namedRoute namedPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, provenanceUnary, localNameUnary,
      _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
        _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed coverUnary refinementUnary ledgerRoute
  have scaleUnary : UnaryHistory scaleRead :=
    unary_cont_closed ledgerUnary lebesgueUnary scaleRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed scaleUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row ledgerRead ∨ hsame row scaleRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover refinement ledgerRead ∧
              Cont ledgerRead lebesgue scaleRead ∧ Cont scaleRead localName namedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, ledgerRoute, scaleRoute, namedRoute, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, ledgerUnary, scaleUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
