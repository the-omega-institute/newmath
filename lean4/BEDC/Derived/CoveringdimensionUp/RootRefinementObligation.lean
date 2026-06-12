import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootRefinementObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinementRead orderRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement refinementRead →
        Cont refinementRead orderBound orderRead →
          Cont orderRead lebesgue handoffRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                        hsame row lebesgue ∨ hsame row refinementRead ∨
                          hsame row orderRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont cover refinement refinementRead ∧
                        Cont refinementRead orderBound orderRead ∧
                          Cont orderRead lebesgue handoffRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory refinementRead ∧ UnaryHistory orderRead ∧
                    UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refinementRoute orderRoute handoffRoute provenancePkg localNamePkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary refinementUnary refinementRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementReadUnary orderUnary orderRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed orderReadUnary lebesgueUnary handoffRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffReadUnary⟩
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
          ⟨source.right, refinementRoute, orderRoute, handoffRoute, provenancePkg,
            localNamePkg⟩
    }
  · exact ⟨refinementReadUnary, orderReadUnary, handoffReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
