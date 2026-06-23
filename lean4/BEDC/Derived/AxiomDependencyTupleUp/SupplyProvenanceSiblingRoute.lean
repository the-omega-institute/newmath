import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleSupplyProvenanceSiblingRoute [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName socketRead supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont supply localName socketRead →
        Cont socketRead supply supplyRead →
          PkgSig bundle socketRead pkg →
            PkgSig bundle supplyRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row supply ∨ hsame row socketRead ∨ hsame row witness ∨
                      hsame row supplyRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont supply localName socketRead ∧
                      Cont socketRead supply supplyRead ∧ PkgSig bundle socketRead pkg ∧
                        PkgSig bundle supplyRead pkg)
                  hsame ∧
                UnaryHistory socketRead ∧ UnaryHistory supplyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier supplySocket socketSupply socketPkg supplyReadPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
    _provenancePkg⟩ := carrier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed supplyUnary localNameUnary supplySocket
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed socketUnary supplyUnary socketSupply
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row supply ∨ hsame row socketRead ∨ hsame row witness ∨
              hsame row supplyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont supply localName socketRead ∧
              Cont socketRead supply supplyRead ∧ PkgSig bundle socketRead pkg ∧
                PkgSig bundle supplyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supplyRead
        ⟨hsame_refl supplyRead, supplyReadUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, supplySocket, socketSupply, socketPkg, supplyReadPkg⟩
  }
  exact ⟨cert, socketUnary, supplyReadUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
