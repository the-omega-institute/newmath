import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleHostSupplyNonescape [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      Cont supply localName hostRead ->
        PkgSig bundle hostRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row supply ∨ hsame row localName ∨ hsame row hostRead)
              (fun row : BHist =>
                hsame row hostRead ∧ Cont supply localName hostRead ∧
                  PkgSig bundle hostRead pkg)
              hsame ∧
            UnaryHistory supply ∧ UnaryHistory localName ∧ UnaryHistory hostRead ∧
              Cont mode witness route ∧ Cont route supply localName ∧
                Cont supply localName hostRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier supplyLocalHost hostPkg
  obtain
    ⟨_modeCases, _modeUnary, _witnessUnary, supplyUnary, _transportUnary, _routeUnary,
      localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
      provenancePkg⟩ := carrier
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed supplyUnary localNameUnary supplyLocalHost
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hostRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row supply ∨ hsame row localName ∨ hsame row hostRead)
          (fun row : BHist =>
            hsame row hostRead ∧ Cont supply localName hostRead ∧
              PkgSig bundle hostRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro hostRead ⟨hsame_refl hostRead, hostReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
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
      exact ⟨source.left, supplyLocalHost, hostPkg⟩
  }
  exact
    ⟨cert, supplyUnary, localNameUnary, hostReadUnary, modeWitnessRoute,
      routeSupplyLocalName, supplyLocalHost, provenancePkg, hostPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
