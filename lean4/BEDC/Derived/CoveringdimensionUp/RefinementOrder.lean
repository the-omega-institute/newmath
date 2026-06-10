import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRefinementOrder [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead coverRead refinementRead orderRead dimensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead cover coverRead →
          Cont coverRead refinement refinementRead →
            Cont refinementRead orderBound orderRead →
              Cont orderRead lebesgue dimensionRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle localName pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row dimensionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                            hsame row refinement ∨ hsame row orderBound ∨
                              hsame row lebesgue ∨ hsame row dimensionRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
                            Cont compactRead cover coverRead ∧
                              Cont coverRead refinement refinementRead ∧
                                Cont refinementRead orderBound orderRead ∧
                                  Cont orderRead lebesgue dimensionRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory coverRead ∧
                        UnaryHistory refinementRead ∧ UnaryHistory orderRead ∧
                          UnaryHistory dimensionRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute coverRoute refinementRoute orderRoute dimensionRoute
    provenancePkg localNamePkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactReadUnary coverUnary coverRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverReadUnary refinementUnary refinementRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementReadUnary orderUnary orderRoute
  have dimensionReadUnary : UnaryHistory dimensionRead :=
    unary_cont_closed orderReadUnary lebesgueUnary dimensionRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro dimensionRead ⟨hsame_refl dimensionRead, dimensionReadUnary⟩
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
          ⟨source.right, compactRoute, coverRoute, refinementRoute, orderRoute,
            dimensionRoute, provenancePkg, localNamePkg⟩
    }
  · exact
      ⟨compactReadUnary, coverReadUnary, refinementReadUnary, orderReadUnary,
        dimensionReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
