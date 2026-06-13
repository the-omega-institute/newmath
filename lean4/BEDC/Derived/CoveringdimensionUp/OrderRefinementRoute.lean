import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionOrderRefinementRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead coverRead refinedMember orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead cover coverRead →
          Cont coverRead refinement refinedMember →
            Cont refinedMember orderBound orderRead →
              PkgSig bundle orderRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨
                        hsame row metricRead ∨ hsame row cover ∨ hsame row coverRead ∨
                          hsame row refinement ∨ hsame row refinedMember ∨
                            hsame row orderBound ∨ hsame row orderRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                        Cont metricRead cover coverRead ∧
                          Cont coverRead refinement refinedMember ∧
                            Cont refinedMember orderBound orderRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle orderRead pkg)
                    hsame ∧ UnaryHistory metricRead ∧ UnaryHistory coverRead ∧
                  UnaryHistory refinedMember ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute coverRoute refinedRoute orderRoute orderPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed metricUnary coverUnary coverRoute
  have refinedUnary : UnaryHistory refinedMember :=
    unary_cont_closed coverReadUnary refinementUnary refinedRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinedUnary orderUnary orderRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro orderRead ⟨hsame_refl orderRead, orderReadUnary⟩
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
          ⟨source.right, metricRoute, coverRoute, refinedRoute, orderRoute,
            provenancePkg, orderPkg⟩
    }
  · exact ⟨metricUnary, coverReadUnary, refinedUnary, orderReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
