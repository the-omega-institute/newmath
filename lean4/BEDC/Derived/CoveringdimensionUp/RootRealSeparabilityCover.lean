import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverRefinementTree [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName coverRead refinementRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover coverRead →
        Cont coverRead refinement refinementRead →
          Cont refinementRead localName namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row coverRead ∨ hsame row refinement ∨
                      hsame row refinementRead ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont epsilonNet cover coverRead ∧
                      Cont coverRead refinement refinementRead ∧
                        Cont refinementRead localName namedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory coverRead ∧ UnaryHistory refinementRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier epsilonCoverRead coverReadRefinement refinementLocalName namedReadPkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverRead
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverReadUnary refinementUnary coverReadRefinement
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed refinementReadUnary localNameUnary refinementLocalName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row coverRead ∨ hsame row refinement ∨
              hsame row refinementRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilonNet cover coverRead ∧
              Cont coverRead refinement refinementRead ∧ Cont refinementRead localName namedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, epsilonCoverRead, coverReadRefinement, refinementLocalName,
          provenancePkg, namedReadPkg⟩
  }
  exact ⟨cert, coverReadUnary, refinementReadUnary, namedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
