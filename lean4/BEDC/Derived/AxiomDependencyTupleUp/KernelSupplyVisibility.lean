import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleKernelSupplyVisibility [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont supply witness kernelRead →
        PkgSig bundle kernelRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                  hsame row kernelRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
                  Cont supply witness kernelRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle kernelRead pkg)
              hsame ∧
            UnaryHistory kernelRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier supplyWitnessKernel kernelPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed supplyUnary witnessUnary supplyWitnessKernel
  have sourceKernel :
      (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row) kernelRead := by
    exact ⟨hsame_refl kernelRead, kernelUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨ hsame row kernelRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              Cont supply witness kernelRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle kernelRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro kernelRead sourceKernel
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
      exact
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, supplyWitnessKernel,
          provenancePkg, kernelPkg⟩
  }
  exact ⟨cert, kernelUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
