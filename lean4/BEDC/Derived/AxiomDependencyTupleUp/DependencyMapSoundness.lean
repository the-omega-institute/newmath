import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleDependencyMapSoundness [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName modeRead supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont mode witness modeRead →
        Cont modeRead supply supplyRead →
          PkgSig bundle supplyRead pkg →
            (hsame mode BHist.Empty ∨ hsame mode (BHist.e0 BHist.Empty) ∨
                hsame mode (BHist.e1 BHist.Empty)) ∧
              SemanticNameCert
                  (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                      hsame row modeRead ∨ hsame row supplyRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont mode witness modeRead ∧
                      Cont modeRead supply supplyRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg)
                  hsame ∧
                UnaryHistory modeRead ∧ UnaryHistory supplyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier modeWitnessRead modeReadSupply supplyReadPkg
  obtain ⟨modeCases, modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have modeReadUnary : UnaryHistory modeRead :=
    unary_cont_closed modeUnary witnessUnary modeWitnessRead
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed modeReadUnary supplyUnary modeReadSupply
  have sourceSupply :
      (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row) supplyRead :=
    ⟨hsame_refl supplyRead, supplyReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
              hsame row modeRead ∨ hsame row supplyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness modeRead ∧
              Cont modeRead supply supplyRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle supplyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supplyRead sourceSupply
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
        ⟨source.right, modeWitnessRead, modeReadSupply, provenancePkg, supplyReadPkg⟩
  }
  exact ⟨modeCases, cert, modeReadUnary, supplyReadUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
