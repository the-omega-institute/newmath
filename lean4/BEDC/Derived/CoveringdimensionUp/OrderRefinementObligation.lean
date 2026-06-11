import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionOrderRefinementObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinedParent orderRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement refinedParent →
        Cont refinedParent orderBound orderRead →
          Cont orderRead localName namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                      hsame row refinedParent ∨ hsame row orderRead ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont cover refinement refinedParent ∧
                      Cont refinedParent orderBound orderRead ∧
                        Cont orderRead localName namedRead ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory refinedParent ∧ UnaryHistory orderRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refinedParentRoute orderRoute namedRoute namedPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have refinedParentUnary : UnaryHistory refinedParent :=
    unary_cont_closed coverUnary refinementUnary refinedParentRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinedParentUnary orderUnary orderRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed orderReadUnary localNameUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
                  (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, refinedParentRoute, orderRoute, namedRoute, namedPkg⟩
    }
  · exact ⟨refinedParentUnary, orderReadUnary, namedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
