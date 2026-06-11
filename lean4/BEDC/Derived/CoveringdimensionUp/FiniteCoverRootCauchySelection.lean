import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverRootCauchySelection [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound realSeal transport replay provenance
      localName metricRead completionRead selectionRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound realSeal
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead realSeal completionRead →
          Cont cover refinement selectionRead →
            Cont completionRead selectionRead namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨
                          hsame row realSeal ∨ hsame row metricRead ∨
                            hsame row completionRead ∨ hsame row selectionRead ∨
                              hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                        Cont metricRead realSeal completionRead ∧
                          Cont cover refinement selectionRead ∧
                            Cont completionRead selectionRead namedRead ∧
                              PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory metricRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory selectionRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute completionRoute selectionRoute namedRoute namedPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderRealReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary realSealUnary completionRoute
  have selectionUnary : UnaryHistory selectionRead :=
    unary_cont_closed coverUnary refinementUnary selectionRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed completionUnary selectionUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row realSeal ∨
                hsame row metricRead ∨ hsame row completionRead ∨
                  hsame row selectionRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead realSeal completionRead ∧
                Cont cover refinement selectionRead ∧
                  Cont completionRead selectionRead namedRead ∧
                    PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨source.right, metricRoute, completionRoute, selectionRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, metricUnary, completionUnary, selectionUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
