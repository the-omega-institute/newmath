import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleNameCertObligations [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      Cont supply witness auditRead ->
        PkgSig bundle auditRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row localName ∧
                  AxiomDependencyTupleCarrier mode witness supply transport route provenance
                    localName bundle pkg)
              (fun row : BHist => hsame row localName)
              (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
              UnaryHistory auditRead ∧ Cont mode witness route ∧ Cont route supply localName ∧
                Cont supply witness auditRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier auditRoute auditPkg
  have carrierWitness :
      AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg := carrier
  obtain ⟨_modeCases, modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocal,
    provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed supplyUnary witnessUnary auditRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row localName ∧
            AxiomDependencyTupleCarrier mode witness supply transport route provenance
              localName bundle pkg)
        (fun row : BHist => hsame row localName)
        (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro localName ⟨hsame_refl localName, carrierWitness⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, modeUnary, witnessUnary, supplyUnary, auditUnary, modeWitnessRoute,
      routeSupplyLocal, auditRoute, provenancePkg, auditPkg⟩

theorem AxiomDependencyTupleExternalSupplyRefusal [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      hsame mode (BHist.e1 BHist.Empty) ->
        Cont localName supply refusedRead ->
          PkgSig bundle refusedRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row refusedRead ∧ UnaryHistory row ∧
                    hsame mode (BHist.e1 BHist.Empty))
                (fun row : BHist => hsame row refusedRead)
                (fun row : BHist => hsame row refusedRead ∧ Cont localName supply refusedRead)
                hsame ∧
              UnaryHistory supply ∧ UnaryHistory localName ∧ UnaryHistory refusedRead ∧
                hsame mode (BHist.e1 BHist.Empty) ∧ Cont mode witness route ∧
                  Cont route supply localName ∧ Cont localName supply refusedRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle refusedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modeC localSupplyRefused refusedPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    localUnary, _transportSame, modeWitnessRoute, routeSupplyLocal, provenancePkg⟩ := carrier
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed localUnary supplyUnary localSupplyRefused
  have sourceAtRefused :
      (fun row : BHist =>
        hsame row refusedRead ∧ UnaryHistory row ∧ hsame mode (BHist.e1 BHist.Empty))
          refusedRead := by
    exact ⟨hsame_refl refusedRead, refusedUnary, modeC⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusedRead ∧ UnaryHistory row ∧ hsame mode (BHist.e1 BHist.Empty))
          (fun row : BHist => hsame row refusedRead)
          (fun row : BHist => hsame row refusedRead ∧ Cont localName supply refusedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedRead sourceAtRefused
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, localSupplyRefused⟩
  }
  exact
    ⟨cert, supplyUnary, localUnary, refusedUnary, modeC, modeWitnessRoute, routeSupplyLocal,
      localSupplyRefused, provenancePkg, refusedPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
