import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTuple_zero_supply_mode_exactness [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName supplyRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName bundle pkg →
      hsame mode BHist.Empty →
        Cont mode supply supplyRead →
          Cont supplyRead witness witnessRead →
            PkgSig bundle witnessRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row BHist.Empty ∨ hsame row supply ∨ hsame row witness ∨
                      hsame row witnessRead)
                  (fun row : BHist => PkgSig bundle witnessRead pkg ∧ hsame row witnessRead)
                  hsame ∧
                UnaryHistory supplyRead ∧ UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier _zeroMode supplyCont witnessCont witnessPkg
  obtain ⟨_modeCases, modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
    _provenancePkg⟩ := carrier
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed modeUnary supplyUnary supplyCont
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed supplyReadUnary witnessUnary witnessCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row BHist.Empty ∨ hsame row supply ∨ hsame row witness ∨
              hsame row witnessRead)
          (fun row : BHist => PkgSig bundle witnessRead pkg ∧ hsame row witnessRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨witnessPkg, source.left⟩
  }
  exact ⟨cert, supplyReadUnary, witnessReadUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
