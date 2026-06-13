import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionSimplicialStarRefinementScope [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName starRead densityRead nerveRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement starRead →
        Cont starRead lebesgue densityRead →
          Cont densityRead orderBound nerveRead →
            Cont nerveRead localName publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨ hsame row starRead ∨
                          hsame row densityRead ∨ hsame row nerveRead ∨
                            hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont cover refinement starRead ∧
                        Cont starRead lebesgue densityRead ∧
                          Cont densityRead orderBound nerveRead ∧
                            Cont nerveRead localName publicRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory starRead ∧ UnaryHistory densityRead ∧
                    UnaryHistory nerveRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRefinementStar starDensity densityNerve nervePublic publicPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, lebesgueUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, _compactEpsilonCover,
    _coverRefinementOrder, _orderLebesgueReplay, _transportReplayProvenance, provenancePkg,
    _localNamePkg⟩ := carrier
  have starUnary : UnaryHistory starRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementStar
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed starUnary lebesgueUnary starDensity
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary orderUnary densityNerve
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed nerveUnary localNameUnary nervePublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row starRead ∨
                hsame row densityRead ∨ hsame row nerveRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover refinement starRead ∧
              Cont starRead lebesgue densityRead ∧ Cont densityRead orderBound nerveRead ∧
                Cont nerveRead localName publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRefinementStar, starDensity, densityNerve, nervePublic,
          provenancePkg, publicPkg⟩
  }
  exact ⟨cert, starUnary, densityUnary, nerveUnary, publicUnary⟩

end BEDC.Derived.CoveringdimensionUp
