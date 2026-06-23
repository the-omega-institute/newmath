import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleDownstreamConsumerSupplyBoundary [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont route localName consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                  hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row localName ∨ hsame row consumer)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
                  Cont route localName consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier routeLocalConsumer consumerPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, _supplyUnary, _transportUnary,
    routeUnary, localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary localNameUnary routeLocalConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              Cont route localName consumer ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceConsumer
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, routeLocalConsumer,
          provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
