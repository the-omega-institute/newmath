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

theorem CoveringDimensionRootCoverScopePackage [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityRead nerveRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont orderBound lebesgue densityRead →
        Cont densityRead localName nerveRead →
          Cont nerveRead replay scopeRead →
            PkgSig bundle scopeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row orderBound ∨
                        hsame row densityRead ∨ hsame row nerveRead ∨ hsame row scopeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle scopeRead pkg)
                  hsame ∧ UnaryHistory densityRead ∧ UnaryHistory nerveRead ∧
                UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier densityRoute nerveRoute scopeRoute scopePkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed orderUnary lebesgueUnary densityRoute
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary localNameUnary nerveRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed nerveUnary replayUnary scopeRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, scopePkg⟩
    }
  · exact ⟨densityUnary, nerveUnary, scopeUnary⟩

end BEDC.Derived.CoveringDimensionUp
