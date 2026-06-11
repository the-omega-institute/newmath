import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSeparabilityCoveringDimensionForwardRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName denseWindow finiteCover refinementRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet denseWindow →
        Cont denseWindow cover finiteCover →
          Cont finiteCover refinement refinementRead →
            Cont refinementRead localName nameRead →
              PkgSig bundle nameRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row denseWindow ∨
                          hsame row finiteCover ∨ hsame row refinementRead ∨
                            hsame row nameRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet denseWindow ∧
                        Cont denseWindow cover finiteCover ∧
                          Cont finiteCover refinement refinementRead ∧
                            Cont refinementRead localName nameRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle nameRead pkg)
                    hsame ∧
                  UnaryHistory denseWindow ∧ UnaryHistory finiteCover ∧
                    UnaryHistory refinementRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactEpsilonDense denseCoverFinite finiteRefinementRead
    refinementNameRead nameReadPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have denseUnary : UnaryHistory denseWindow :=
    unary_cont_closed compactUnary epsilonUnary compactEpsilonDense
  have finiteCoverUnary : UnaryHistory finiteCover :=
    unary_cont_closed denseUnary coverUnary denseCoverFinite
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed finiteCoverUnary refinementUnary finiteRefinementRead
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed refinementReadUnary localNameUnary refinementNameRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row denseWindow ∨ hsame row finiteCover ∨
                hsame row refinementRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet denseWindow ∧
              Cont denseWindow cover finiteCover ∧ Cont finiteCover refinement refinementRead ∧
                Cont refinementRead localName nameRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nameRead ⟨hsame_refl nameRead, nameReadUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactEpsilonDense, denseCoverFinite, finiteRefinementRead,
          refinementNameRead, provenancePkg, nameReadPkg⟩
  }
  exact ⟨cert, denseUnary, finiteCoverUnary, refinementReadUnary, nameReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
