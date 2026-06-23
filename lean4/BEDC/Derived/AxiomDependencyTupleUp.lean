import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyTupleCarrier [AskSetup] [PackageSetup]
    (mode witness supply transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  (hsame mode BHist.Empty ∨
      hsame mode (BHist.e0 BHist.Empty) ∨ hsame mode (BHist.e1 BHist.Empty)) ∧
    UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory localName ∧
        hsame transport transport ∧ Cont mode witness route ∧ Cont route supply localName ∧
          PkgSig bundle provenance pkg

theorem AxiomDependencyTupleCarrier_mode_exhaustion [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      (hsame mode BHist.Empty ∨ hsame mode (BHist.e0 BHist.Empty) ∨
          hsame mode (BHist.e1 BHist.Empty)) ∧
        UnaryHistory witness ∧ UnaryHistory supply ∧ UnaryHistory route ∧
          UnaryHistory localName ∧ Cont mode witness route ∧
            Cont route supply localName ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier
  rcases carrier with
    ⟨modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, routeUnary,
      localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
      provenancePkg⟩
  exact
    ⟨modeCases, witnessUnary, supplyUnary, routeUnary, localNameUnary, modeWitnessRoute,
      routeSupplyLocalName, provenancePkg⟩

theorem AxiomDependencyTupleCounterexampleSocketNonexport [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName audit escape : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont witness supply audit →
        Cont audit route escape →
          PkgSig bundle escape pkg →
            UnaryHistory witness ∧ UnaryHistory supply ∧ UnaryHistory audit ∧
              UnaryHistory escape ∧ Cont witness supply audit ∧ Cont audit route escape ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle escape pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier witnessSupplyAudit auditRouteEscape escapePkg
  obtain
    ⟨_modeCases, witnessUnary, supplyUnary, routeUnary, _localNameUnary, _modeWitnessRoute,
      _routeSupplyLocalName, provenancePkg⟩ :=
    AxiomDependencyTupleCarrier_mode_exhaustion carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed witnessUnary supplyUnary witnessSupplyAudit
  have escapeUnary : UnaryHistory escape :=
    unary_cont_closed auditUnary routeUnary auditRouteEscape
  exact
    ⟨witnessUnary, supplyUnary, auditUnary, escapeUnary, witnessSupplyAudit, auditRouteEscape,
      provenancePkg, escapePkg⟩

theorem AxiomDependencyTupleRestrictedSupplyLedger_exactness [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      hsame mode (BHist.e0 BHist.Empty) →
        Cont supply route supplyRead →
          PkgSig bundle supplyRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                    hsame row supplyRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg)
                hsame ∧
              UnaryHistory supplyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier _restrictedMode supplyRouteRead supplyReadPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, supplyUnary, _transportUnary, routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed supplyUnary routeUnary supplyRouteRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supplyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨ hsame row supplyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supplyRead ⟨hsame_refl supplyRead, supplyReadUnary⟩
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
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, provenancePkg, supplyReadPkg⟩
  }
  exact ⟨cert, supplyReadUnary⟩

theorem AxiomDependencyTupleHsameContScope [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      Cont transport route replayRead ->
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory replayRead ∧
          hsame transport transport ∧ Cont mode witness route ∧
            Cont route supply localName ∧ Cont transport route replayRead ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier transportRouteReplay
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, _supplyUnary, transportUnary,
    routeUnary, _localNameUnary, transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary routeUnary transportRouteReplay
  exact
    ⟨transportUnary, routeUnary, replayUnary, transportSame, modeWitnessRoute,
      routeSupplyLocalName, transportRouteReplay, provenancePkg⟩

theorem AxiomDependencyTupleRestrictedSupplyLedgerTotality [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName supplyRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      hsame mode (BHist.e0 BHist.Empty) →
        Cont supply route supplyRead →
          Cont supplyRead localName namedRead →
            PkgSig bundle supplyRead pkg →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                        hsame row route ∨ hsame row supplyRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont mode witness route ∧
                        Cont route supply localName ∧ Cont supply route supplyRead ∧
                          Cont supplyRead localName namedRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle supplyRead pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory supplyRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier _restrictedMode supplyRouteRead supplyReadNamed supplyReadPkg namedReadPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, supplyUnary, _transportUnary, routeUnary,
    localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed supplyUnary routeUnary supplyRouteRead
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed supplyReadUnary localNameUnary supplyReadNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨ hsame row route ∨
              hsame row supplyRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              Cont supply route supplyRead ∧ Cont supplyRead localName namedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, supplyRouteRead,
          supplyReadNamed, provenancePkg, supplyReadPkg, namedReadPkg⟩
  }
  exact ⟨cert, supplyReadUnary, namedReadUnary⟩

theorem AxiomDependencyTupleRootUnblockSpine [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      Cont route localName rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                  hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row localName ∨ hsame row rootRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont mode witness route ∧
                  Cont route supply localName ∧ Cont route localName rootRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
              hsame ∧
            UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeLocalRoot rootReadPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, _supplyUnary, _transportUnary,
    routeUnary, localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalRoot
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨ hsame row transport ∨
              hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              Cont route localName rootRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootReadUnary⟩
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
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, routeLocalRoot,
          provenancePkg, rootReadPkg⟩
  }
  exact ⟨cert, rootReadUnary⟩

theorem AxiomDependencyTupleAuditMapRowCoverage [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName replayRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont transport route replayRead →
        Cont replayRead localName auditRead →
          PkgSig bundle auditRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row mode ∨ hsame row witness ∨ hsame row supply ∨
                    hsame row transport ∨ hsame row route ∨ hsame row localName ∨
                      hsame row replayRead ∨ hsame row auditRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont mode witness route ∧
                    Cont route supply localName ∧ Cont transport route replayRead ∧
                      Cont replayRead localName auditRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg)
                hsame ∧
              UnaryHistory replayRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportRouteReplay replayLocalAudit auditReadPkg
  obtain ⟨_modeCases, _modeUnary, _witnessUnary, _supplyUnary, transportUnary,
    routeUnary, localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary routeUnary transportRouteReplay
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed replayUnary localNameUnary replayLocalAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mode ∨ hsame row witness ∨ hsame row supply ∨ hsame row transport ∨
              hsame row route ∨ hsame row localName ∨ hsame row replayRead ∨
                hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mode witness route ∧ Cont route supply localName ∧
              Cont transport route replayRead ∧ Cont replayRead localName auditRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
        ⟨source.right, modeWitnessRoute, routeSupplyLocalName, transportRouteReplay,
          replayLocalAudit, provenancePkg, auditReadPkg⟩
  }
  exact ⟨cert, replayUnary, auditUnary⟩

end BEDC.Derived.AxiomDependencyTupleUp
