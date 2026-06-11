import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootSimplicialCoverHandoff [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName nerveRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound nerveRead →
        Cont nerveRead localName handoffRead →
          PkgSig bundle handoffRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row orderBound ∨ hsame row nerveRead ∨
                    hsame row localName ∨ hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont cover orderBound nerveRead ∧
                    Cont nerveRead localName handoffRead ∧ PkgSig bundle handoffRead pkg)
                hsame ∧
              UnaryHistory nerveRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverOrderNerve nerveLocalHandoff handoffPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed coverUnary orderUnary coverOrderNerve
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed nerveUnary localNameUnary nerveLocalHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row orderBound ∨ hsame row nerveRead ∨
              hsame row localName ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover orderBound nerveRead ∧
              Cont nerveRead localName handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverOrderNerve, nerveLocalHandoff, handoffPkg⟩
  }
  exact ⟨cert, nerveUnary, handoffUnary⟩

end BEDC.Derived.CoveringdimensionUp
