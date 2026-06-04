import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
    UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory lebesgue ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont compactMetric epsilonNet cover ∧
          Cont cover refinement orderBound ∧ Cont orderBound lebesgue replay ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem CoveringDimensionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound
              lebesgue transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound
              lebesgue transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport localNameUnary (hsame_symm source.right), localNamePkg⟩
  }

theorem CoveringDimensionFiniteEpsilonNetCarrier [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName sample : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover sample →
        PkgSig bundle sample pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row epsilonNet ∨ hsame row cover ∨ hsame row refinement ∨
                  hsame row orderBound ∨ hsame row sample)
              (fun row : BHist => UnaryHistory row)
              (fun row : BHist => PkgSig bundle localName pkg ∨ PkgSig bundle sample pkg)
              hsame ∧
            UnaryHistory sample := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonCoverSample samplePkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have sampleUnary : UnaryHistory sample :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverSample
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro epsilonNet (Or.inl (hsame_refl epsilonNet))
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
          intro row other sameRows source
          cases source with
          | inl epsilonSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) epsilonSource)
          | inr rest =>
              cases rest with
              | inl coverSource =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) coverSource))
              | inr rest =>
                  cases rest with
                  | inl refinementSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) refinementSource)))
                  | inr rest =>
                      cases rest with
                      | inl orderSource =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) orderSource))))
                      | inr sampleSource =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (hsame_trans (hsame_symm sameRows) sampleSource))))
      }
      pattern_sound := by
        intro row source
        cases source with
        | inl epsilonSource =>
            exact unary_transport epsilonUnary (hsame_symm epsilonSource)
        | inr rest =>
            cases rest with
            | inl coverSource =>
                exact unary_transport coverUnary (hsame_symm coverSource)
            | inr rest =>
                cases rest with
                | inl refinementSource =>
                    exact unary_transport refinementUnary (hsame_symm refinementSource)
                | inr rest =>
                    cases rest with
                    | inl orderSource =>
                        exact unary_transport orderUnary (hsame_symm orderSource)
                    | inr sampleSource =>
                        exact unary_transport sampleUnary (hsame_symm sampleSource)
      ledger_sound := by
        intro row source
        cases source with
        | inl _epsilonSource =>
            exact Or.inl localNamePkg
        | inr rest =>
            cases rest with
            | inl _coverSource =>
                exact Or.inl localNamePkg
            | inr rest =>
                cases rest with
                | inl _refinementSource =>
                    exact Or.inl localNamePkg
                | inr rest =>
                    cases rest with
                    | inl _orderSource =>
                        exact Or.inl localNamePkg
                    | inr _sampleSource =>
                        exact Or.inr samplePkg
    }
  · exact sampleUnary

end BEDC.Derived.CoveringdimensionUp
