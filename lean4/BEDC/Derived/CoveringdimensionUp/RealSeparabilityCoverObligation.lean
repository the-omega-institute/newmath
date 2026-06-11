import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityCoverObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityWindow coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover densityWindow →
        Cont densityWindow refinement coverRead →
          PkgSig bundle coverRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                    hsame row refinement ∨ hsame row orderBound ∨ hsame row densityWindow ∨
                      hsame row coverRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
                    Cont epsilonNet cover densityWindow ∧
                      Cont densityWindow refinement coverRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle coverRead pkg)
                hsame ∧
              UnaryHistory densityWindow ∧ UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier epsilonCoverDensity densityRefinementRead coverReadPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityWindow :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverDensity
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed densityUnary refinementUnary densityRefinementRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row densityWindow ∨
                hsame row coverRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
              Cont epsilonNet cover densityWindow ∧
                Cont densityWindow refinement coverRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle coverRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverRead ⟨hsame_refl coverRead, coverReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactEpsilonCover, epsilonCoverDensity, densityRefinementRead,
          provenancePkg, coverReadPkg⟩
  }
  exact ⟨cert, densityUnary, coverReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
