import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteEpsilonNetRefinementHandoff [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName sample refinedSample : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover sample →
        Cont sample refinement refinedSample →
          PkgSig bundle sample pkg →
            PkgSig bundle refinedSample pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row refinedSample ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row epsilonNet ∨ hsame row cover ∨ hsame row refinement ∨
                      hsame row orderBound ∨ hsame row sample ∨ hsame row refinedSample)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle sample pkg ∧ PkgSig bundle refinedSample pkg ∧
                        Cont sample refinement refinedSample)
                  hsame ∧
                UnaryHistory sample ∧ UnaryHistory refinedSample := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonCoverSample sampleRefinement refinedPkg samplePkg
  have finiteSample :
      SemanticNameCert
          (fun row : BHist =>
            hsame row epsilonNet ∨ hsame row cover ∨ hsame row refinement ∨
              hsame row orderBound ∨ hsame row sample)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle localName pkg ∨ PkgSig bundle sample pkg)
          hsame ∧
        UnaryHistory sample :=
    CoveringDimensionFiniteEpsilonNetCarrier carrier epsilonCoverSample refinedPkg
  obtain ⟨_sampleCert, sampleUnary⟩ := finiteSample
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have refinedUnary : UnaryHistory refinedSample :=
    unary_cont_closed sampleUnary refinementUnary sampleRefinement
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedSample ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilonNet ∨ hsame row cover ∨ hsame row refinement ∨
              hsame row orderBound ∨ hsame row sample ∨ hsame row refinedSample)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle sample pkg ∧
              PkgSig bundle refinedSample pkg ∧ Cont sample refinement refinedSample)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedSample ⟨hsame_refl refinedSample, refinedUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, refinedPkg, samplePkg, sampleRefinement⟩
  }
  exact ⟨cert, sampleUnary, refinedUnary⟩

end BEDC.Derived.CoveringdimensionUp
