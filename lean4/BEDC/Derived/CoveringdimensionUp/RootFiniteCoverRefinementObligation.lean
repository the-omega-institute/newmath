import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootFiniteCoverRefinementObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinementRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet cover →
        Cont cover refinement refinementRead →
          Cont refinementRead orderBound orderRead →
            PkgSig bundle orderRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row refinementRead ∨
                        hsame row orderBound ∨ hsame row orderRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
                      Cont cover refinement refinementRead ∧
                        Cont refinementRead orderBound orderRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle orderRead pkg)
                  hsame ∧
                UnaryHistory refinementRead ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactCoverRoute refinementRoute orderRoute orderPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary refinementUnary refinementRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementReadUnary orderUnary orderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row refinementRead ∨ hsame row orderBound ∨
                hsame row orderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
              Cont cover refinement refinementRead ∧
                Cont refinementRead orderBound orderRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle orderRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro orderRead ⟨hsame_refl orderRead, orderReadUnary⟩
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
        ⟨source.right, compactCoverRoute, refinementRoute, orderRoute, provenancePkg,
          orderPkg⟩
  }
  exact ⟨cert, refinementReadUnary, orderReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
