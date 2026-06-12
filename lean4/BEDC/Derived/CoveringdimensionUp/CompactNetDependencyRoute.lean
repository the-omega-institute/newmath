import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactNetDependencyRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRoot coverRead refinementRead orderRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRoot →
        Cont compactRoot cover coverRead →
          Cont coverRead refinement refinementRead →
            Cont refinementRead orderBound orderRead →
              Cont orderRead lebesgue consumerRead →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row compactMetric ∨ hsame row epsilonNet ∨
                          hsame row cover ∨ hsame row refinement ∨
                            hsame row orderBound ∨ hsame row lebesgue ∨
                              hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont compactMetric epsilonNet compactRoot ∧
                          Cont compactRoot cover coverRead ∧
                            Cont coverRead refinement refinementRead ∧
                              Cont refinementRead orderBound orderRead ∧
                                Cont orderRead lebesgue consumerRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle consumerRead pkg)
                      hsame ∧
                    UnaryHistory compactRoot ∧ UnaryHistory coverRead ∧
                      UnaryHistory refinementRead ∧ UnaryHistory orderRead ∧
                        UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRootRoute coverReadRoute refinementReadRoute orderReadRoute
    consumerRoute consumerPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactRootUnary : UnaryHistory compactRoot :=
    unary_cont_closed compactUnary epsilonUnary compactRootRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactRootUnary coverUnary coverReadRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverReadUnary refinementUnary refinementReadRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementReadUnary orderUnary orderReadRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed orderReadUnary lebesgueUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet compactRoot ∧
              Cont compactRoot cover coverRead ∧ Cont coverRead refinement refinementRead ∧
                Cont refinementRead orderBound orderRead ∧
                  Cont orderRead lebesgue consumerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRootRoute, coverReadRoute, refinementReadRoute,
          orderReadRoute, consumerRoute, provenancePkg, consumerPkg⟩
  }
  exact
    ⟨cert, compactRootUnary, coverReadUnary, refinementReadUnary, orderReadUnary,
      consumerReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
