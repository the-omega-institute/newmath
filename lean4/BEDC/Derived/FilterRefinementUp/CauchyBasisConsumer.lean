import BEDC.Derived.FilterRefinementUp.CauchyPreservation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterRefinementCauchyBasisConsumer [AskSetup] [PackageSetup]
    {source target refinement reverse transport replay provenance localName basisRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterRefinementCarrier source target refinement reverse transport replay provenance
        localName bundle pkg ->
      Cont target refinement basisRead ->
        Cont basisRead localName consumerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row basisRead ∨ hsame row consumerRead ∨ hsame row target ∨
                  hsame row refinement)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont target refinement basisRead ∧
                  Cont basisRead localName consumerRead)
              hsame ∧
            UnaryHistory basisRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: FilterRefinementCarrier BHist Cont hsame SemanticNameCert
  intro carrier basisRoute consumerRoute
  obtain ⟨_sourceUnary, targetUnary, refinementUnary, _reverseUnary, _transportUnary,
      _replayUnary, _provenanceUnary, localNameUnary, _targetRefinementSource,
      _sourceReverseReplay, _transportReplayLocalName, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed targetUnary refinementUnary basisRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed basisUnary localNameUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basisRead ∨ hsame row consumerRead ∨ hsame row target ∨
              hsame row refinement)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont target refinement basisRead ∧
              Cont basisRead localName consumerRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, basisRoute, consumerRoute⟩
  }
  exact ⟨cert, basisUnary, consumerUnary⟩

end BEDC.Derived.FilterRefinementUp
