import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleSubjectReductionSocketDependencyRoute [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      hsame mode (BHist.e1 BHist.Empty) →
        Cont supply localName socketRead →
          PkgSig bundle socketRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row socketRead ∧ UnaryHistory row ∧
                    hsame mode (BHist.e1 BHist.Empty))
                (fun row : BHist =>
                  hsame row supply ∨ hsame row socketRead ∨ hsame row witness)
                (fun row : BHist =>
                  hsame row socketRead ∧ Cont supply localName socketRead ∧
                    PkgSig bundle socketRead pkg)
                hsame ∧
              UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modeSocket supplyLocalSocket socketPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocal,
    _provenancePkg⟩ := carrier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed supplyUnary localNameUnary supplyLocalSocket
  have sourceAtSocket :
      (fun row : BHist =>
        hsame row socketRead ∧ UnaryHistory row ∧ hsame mode (BHist.e1 BHist.Empty))
          socketRead := by
    exact ⟨hsame_refl socketRead, socketUnary, modeSocket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socketRead ∧ UnaryHistory row ∧ hsame mode (BHist.e1 BHist.Empty))
          (fun row : BHist =>
            hsame row supply ∨ hsame row socketRead ∨ hsame row witness)
          (fun row : BHist =>
            hsame row socketRead ∧ Cont supply localName socketRead ∧
              PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceAtSocket
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
            unary_transport source.right.left sameRows, source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, supplyLocalSocket, socketPkg⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
