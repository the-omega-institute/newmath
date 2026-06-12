import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverScopeLock [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead densityRead nerveRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound rootRead →
        Cont rootRead provenance densityRead →
          Cont densityRead localName nerveRead →
            Cont nerveRead replay scopeRead →
              PkgSig bundle scopeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨ hsame row densityRead ∨
                          hsame row nerveRead ∨ hsame row scopeRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont cover orderBound rootRead ∧
                        Cont rootRead provenance densityRead ∧
                          Cont densityRead localName nerveRead ∧
                            Cont nerveRead replay scopeRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle scopeRead pkg)
                    hsame ∧
                  UnaryHistory rootRead ∧ UnaryHistory densityRead ∧
                    UnaryHistory nerveRead ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverOrderRoot rootDensity densityNerve nerveScope scopePkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary orderUnary coverOrderRoot
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed rootUnary provenanceUnary rootDensity
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary localNameUnary densityNerve
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed nerveUnary replayUnary nerveScope
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row densityRead ∨
                hsame row nerveRead ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover orderBound rootRead ∧
              Cont rootRead provenance densityRead ∧ Cont densityRead localName nerveRead ∧
                Cont nerveRead replay scopeRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
        ⟨source.right, coverOrderRoot, rootDensity, densityNerve, nerveScope,
          provenancePkg, scopePkg⟩
  }
  exact ⟨cert, rootUnary, densityUnary, nerveUnary, scopeUnary⟩

end BEDC.Derived.CoveringdimensionUp
