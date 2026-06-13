import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringDimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CoveringdimensionUp

theorem CoveringDimensionSeparabilityCoverRefinementRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityRead refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover densityRead →
        Cont densityRead refinement refinementRead →
          PkgSig bundle refinementRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                    hsame row refinement ∨ hsame row lebesgue ∨ hsame row densityRead ∨
                      hsame row refinementRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
                    Cont epsilonNet cover densityRead ∧
                      Cont densityRead refinement refinementRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle refinementRead pkg)
                hsame ∧
              UnaryHistory densityRead ∧ UnaryHistory refinementRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier densityRoute refinementRoute refinementPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed epsilonUnary coverUnary densityRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed densityUnary refinementUnary refinementRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinementRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row lebesgue ∨ hsame row densityRead ∨
                hsame row refinementRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
              Cont epsilonNet cover densityRead ∧
                Cont densityRead refinement refinementRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle refinementRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactEpsilonCover, densityRoute, refinementRoute,
          provenancePkg, refinementPkg⟩
  }
  exact ⟨cert, densityUnary, refinementReadUnary⟩

end BEDC.Derived.CoveringDimensionUp
