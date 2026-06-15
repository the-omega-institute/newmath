import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverLedgerFactorization [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont lebesgue orderBound ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row lebesgue ∨ hsame row orderBound ∨ hsame row ledgerRead)
              (fun row : BHist => UnaryHistory row)
              (fun _row : BHist => PkgSig bundle localName pkg ∨ PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier lebesgueOrderLedger ledgerPkg
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed lebesgueUnary orderUnary lebesgueOrderLedger
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro lebesgue (Or.inl (hsame_refl lebesgue))
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
          | inl lebesgueSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) lebesgueSource)
          | inr rest =>
              cases rest with
              | inl orderSource =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) orderSource))
              | inr ledgerSource =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) ledgerSource))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl lebesgueSource =>
            exact unary_transport lebesgueUnary (hsame_symm lebesgueSource)
        | inr rest =>
            cases rest with
            | inl orderSource =>
                exact unary_transport orderUnary (hsame_symm orderSource)
            | inr ledgerSource =>
                exact unary_transport ledgerUnary (hsame_symm ledgerSource)
      ledger_sound := by
        intro _row source
        cases source with
        | inl _lebesgueSource =>
            exact Or.inl localNamePkg
        | inr rest =>
            cases rest with
            | inl _orderSource =>
                exact Or.inl localNamePkg
            | inr _ledgerSource =>
                exact Or.inr ledgerPkg
    }
  · exact ledgerUnary

end BEDC.Derived.CoveringdimensionUp
