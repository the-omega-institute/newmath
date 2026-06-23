import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleZeroSupplyRowSeparation [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName zeroRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      hsame mode BHist.Empty →
        Cont mode supply zeroRead →
          Cont zeroRead witness refusedRead →
            PkgSig bundle zeroRead pkg →
              PkgSig bundle refusedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row mode ∨ hsame row supply ∨ hsame row zeroRead ∨
                        hsame row refusedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont mode supply zeroRead ∧
                        Cont zeroRead witness refusedRead ∧ PkgSig bundle zeroRead pkg ∧
                          PkgSig bundle refusedRead pkg)
                    hsame ∧
                  UnaryHistory zeroRead ∧ UnaryHistory refusedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _zeroMode modeSupplyZero zeroWitnessRefused zeroPkg refusedPkg
  obtain ⟨_modeCases, modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocal,
    _provenancePkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed modeUnary supplyUnary modeSupplyZero
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed zeroUnary witnessUnary zeroWitnessRefused
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row supply ∨ hsame row zeroRead ∨
              hsame row refusedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode supply zeroRead ∧
              Cont zeroRead witness refusedRead ∧ PkgSig bundle zeroRead pkg ∧
                PkgSig bundle refusedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroRead ⟨hsame_refl zeroRead, zeroUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modeSupplyZero, zeroWitnessRefused, zeroPkg, refusedPkg⟩
  }
  exact ⟨cert, zeroUnary, refusedUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
