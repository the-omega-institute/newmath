import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverPublicScope [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead densityRead nerveRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound rootRead →
        Cont rootRead provenance densityRead →
          Cont densityRead localName nerveRead →
            Cont nerveRead replay publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨
                          hsame row densityRead ∨ hsame row nerveRead ∨
                            hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
                        Cont cover refinement orderBound ∧ Cont cover orderBound rootRead ∧
                          Cont rootRead provenance densityRead ∧
                            Cont densityRead localName nerveRead ∧
                              Cont nerveRead replay publicRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory rootRead ∧ UnaryHistory densityRead ∧
                    UnaryHistory nerveRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverOrderRoot rootDensity densityNerve nervePublic publicPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, replayUnary, provenanceUnary, localNameUnary,
    compactEpsilonCover, coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary orderUnary coverOrderRoot
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed rootUnary provenanceUnary rootDensity
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary localNameUnary densityNerve
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed nerveUnary replayUnary nervePublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row densityRead ∨
                hsame row nerveRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
              Cont cover refinement orderBound ∧ Cont cover orderBound rootRead ∧
                Cont rootRead provenance densityRead ∧ Cont densityRead localName nerveRead ∧
                  Cont nerveRead replay publicRead ∧ PkgSig bundle provenance pkg ∧
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactEpsilonCover, coverRefinementOrder, coverOrderRoot,
          rootDensity, densityNerve, nervePublic, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, rootUnary, densityUnary, nerveUnary, publicUnary⟩

end BEDC.Derived.CoveringdimensionUp
