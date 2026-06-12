import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRefinementMultiplicityWindow [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement refinementRead →
        PkgSig bundle refinementRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                  hsame row refinementRead)
              (fun row : BHist => UnaryHistory row)
              (fun _row : BHist => PkgSig bundle refinementRead pkg ∨
                PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory refinementRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier coverRefinementRead refinementReadPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRead
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro cover (Or.inl (hsame_refl cover))
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
          cases source with
          | inl coverSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) coverSource)
          | inr rest =>
              cases rest with
              | inl refinementSource =>
                  exact
                    Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) refinementSource))
              | inr rest =>
                  cases rest with
                  | inl orderBoundSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) orderBoundSource)))
                  | inr refinementReadSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (hsame_trans (hsame_symm sameRows) refinementReadSource)))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl coverSource =>
            exact unary_transport coverUnary (hsame_symm coverSource)
        | inr rest =>
            cases rest with
            | inl refinementSource =>
                exact unary_transport refinementUnary (hsame_symm refinementSource)
            | inr rest =>
                cases rest with
                | inl orderBoundSource =>
                    exact unary_transport orderUnary (hsame_symm orderBoundSource)
                | inr refinementReadSource =>
                    exact unary_transport refinementReadUnary (hsame_symm refinementReadSource)
      ledger_sound := by
        intro _row source
        cases source with
        | inl _coverSource =>
            exact Or.inr localNamePkg
        | inr rest =>
            cases rest with
            | inl _refinementSource =>
                exact Or.inr localNamePkg
            | inr rest =>
                cases rest with
                | inl _orderBoundSource =>
                    exact Or.inr localNamePkg
                | inr _refinementReadSource =>
                    exact Or.inl refinementReadPkg
    }
  · exact refinementReadUnary

end BEDC.Derived.CoveringdimensionUp
