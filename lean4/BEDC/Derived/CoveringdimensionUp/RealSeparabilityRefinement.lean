import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityRefinement [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName separabilityRead refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound separabilityRead →
        Cont separabilityRead lebesgue refinementRead →
          PkgSig bundle refinementRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                    hsame row orderBound ∨ hsame row lebesgue ∨ hsame row separabilityRead ∨
                      hsame row refinementRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
                    Cont cover refinement orderBound ∧
                      Cont cover orderBound separabilityRead ∧
                        Cont separabilityRead lebesgue refinementRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle refinementRead pkg)
                hsame ∧
              UnaryHistory separabilityRead ∧ UnaryHistory refinementRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier coverOrderSeparability separabilityLebesgueRefinement refinementPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have separabilityUnary : UnaryHistory separabilityRead :=
    unary_cont_closed coverUnary orderUnary coverOrderSeparability
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed separabilityUnary lebesgueUnary separabilityLebesgueRefinement
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row orderBound ∨ hsame row lebesgue ∨ hsame row separabilityRead ∨
                hsame row refinementRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
              Cont cover refinement orderBound ∧ Cont cover orderBound separabilityRead ∧
                Cont separabilityRead lebesgue refinementRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle refinementRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinementRead ⟨hsame_refl refinementRead, refinementReadUnary⟩
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
        ⟨source.right, compactEpsilonCover, coverRefinementOrder, coverOrderSeparability,
          separabilityLebesgueRefinement, provenancePkg, refinementPkg⟩
  }
  exact ⟨cert, separabilityUnary, refinementReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
