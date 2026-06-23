import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleZeroSupplySemanticNameCert [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      hsame mode BHist.Empty →
        Cont witness supply zeroRead →
          PkgSig bundle zeroRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row zeroRead ∧ UnaryHistory row ∧ hsame mode BHist.Empty)
                (fun row : BHist =>
                  hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                    hsame row zeroRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ hsame mode BHist.Empty ∧
                    Cont mode witness route ∧ Cont route supply localName ∧
                      Cont witness supply zeroRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle zeroRead pkg)
                hsame ∧
              UnaryHistory zeroRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier zeroMode witnessSupplyZero zeroReadPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed witnessUnary supplyUnary witnessSupplyZero
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row zeroRead ∧ UnaryHistory row ∧ hsame mode BHist.Empty)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨ hsame row zeroRead)
          (fun row : BHist =>
            UnaryHistory row ∧ hsame mode BHist.Empty ∧ Cont mode witness route ∧
              Cont route supply localName ∧ Cont witness supply zeroRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle zeroRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro zeroRead ⟨hsame_refl zeroRead, zeroReadUnary, zeroMode⟩
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
            unary_transport source.right.left sameRows,
            source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.left, source.right.right, modeWitnessRoute, routeSupplyLocalName,
          witnessSupplyZero, provenancePkg, zeroReadPkg⟩
  }
  exact ⟨cert, zeroReadUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
