import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleCounterexampleSocketBoundary [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      hsame mode (BHist.e1 BHist.Empty) →
        Cont witness supply socketRead →
          PkgSig bundle socketRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row witness ∨ hsame row supply ∨ hsame row socketRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ hsame mode (BHist.e1 BHist.Empty) ∧
                    Cont mode witness route ∧ Cont witness supply socketRead ∧
                      PkgSig bundle socketRead pkg)
                hsame ∧
              UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modeCounterexample witnessSupplySocket socketPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, _routeSupplyLocal,
    _provenancePkg⟩ := carrier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed witnessUnary supplyUnary witnessSupplySocket
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row witness ∨ hsame row supply ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ hsame mode (BHist.e1 BHist.Empty) ∧
              Cont mode witness route ∧ Cont witness supply socketRead ∧
                PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead ⟨hsame_refl socketRead, socketUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modeCounterexample, modeWitnessRoute, witnessSupplySocket,
          socketPkg⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
