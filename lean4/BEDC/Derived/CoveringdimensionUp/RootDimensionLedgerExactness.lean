import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootDimensionLedgerExactness [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead realSealRead nerveRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg ->
      Cont cover refinement metricRead ->
        Cont metricRead orderBound realSealRead ->
          Cont realSealRead lebesgue nerveRead ->
            Cont nerveRead orderBound ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                          hsame row metricRead ∨ hsame row realSealRead ∨
                            hsame row nerveRead ∨ hsame row ledgerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont cover refinement metricRead ∧
                        Cont metricRead orderBound realSealRead ∧
                          Cont realSealRead lebesgue nerveRead ∧
                            Cont nerveRead orderBound ledgerRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
                    hsame ∧
                  UnaryHistory metricRead ∧ UnaryHistory realSealRead ∧
                    UnaryHistory nerveRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRefinementMetric metricOrderRealSeal realSealLebesgueNerve
    nerveOrderLedger ledgerPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementMetric
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed metricUnary orderUnary metricOrderRealSeal
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed realSealUnary lebesgueUnary realSealLebesgueNerve
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed nerveUnary orderUnary nerveOrderLedger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row metricRead ∨ hsame row realSealRead ∨ hsame row nerveRead ∨
                  hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover refinement metricRead ∧
              Cont metricRead orderBound realSealRead ∧
                Cont realSealRead lebesgue nerveRead ∧
                  Cont nerveRead orderBound ledgerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRefinementMetric, metricOrderRealSeal, realSealLebesgueNerve,
          nerveOrderLedger, provenancePkg, ledgerPkg⟩
  }
  exact ⟨cert, metricUnary, realSealUnary, nerveUnary, ledgerUnary⟩

end BEDC.Derived.CoveringdimensionUp
