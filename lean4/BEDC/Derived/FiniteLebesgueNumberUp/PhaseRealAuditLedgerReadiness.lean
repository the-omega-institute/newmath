import BEDC.Derived.FiniteLebesgueNumberUp

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberPhaseRealAuditLedger [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow auditRead phaseRead
      compactRead continuousRead uniformRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont route nameRow auditRead ∧
      Cont auditRead radius phaseRead ∧
        Cont phaseRead mesh compactRead ∧
          Cont compactRead route continuousRead ∧
            Cont continuousRead nameRow uniformRead ∧ PkgSig bundle uniformRead pkg

theorem FiniteLebesgueNumberPhaseRealAuditLedger_certificate [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead
      compactRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberPhaseRealAuditLedger cover window radius mesh transport route
        provenance nameRow auditRead phaseRead compactRead continuousRead uniformRead bundle
        pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberPhaseRealAuditLedger cover window radius mesh transport
                route provenance nameRow auditRead phaseRead compactRead continuousRead
                uniformRead bundle pkg)
          (fun row : BHist =>
            hsame row auditRead ∨ hsame row phaseRead ∨ hsame row compactRead ∨
              hsame row continuousRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame ∧
        UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberPhaseRealAuditLedger cover window radius mesh transport route
        provenance nameRow auditRead phaseRead compactRead continuousRead uniformRead bundle
        pkg :=
    ledger
  obtain ⟨carrier, routeAudit, auditPhase, phaseCompact, compactContinuous,
    continuousUniform, uniformPkg⟩ := ledger
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditPhase
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed phaseUnary meshUnary phaseCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousUniform
  have sourceUniform :
      (fun row : BHist =>
        hsame row uniformRead ∧
          FiniteLebesgueNumberPhaseRealAuditLedger cover window radius mesh transport route
            provenance nameRow auditRead phaseRead compactRead continuousRead uniformRead
            bundle pkg) uniformRead := by
    exact ⟨hsame_refl uniformRead, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberPhaseRealAuditLedger cover window radius mesh transport
                route provenance nameRow auditRead phaseRead compactRead continuousRead
                uniformRead bundle pkg)
          (fun row : BHist =>
            hsame row auditRead ∨ hsame row phaseRead ∨ hsame row compactRead ∨
              hsame row continuousRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact ⟨cert, uniformUnary⟩

theorem FiniteLebesgueNumberPhaseRealAuditLedgerReadiness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead compactRead
      continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow bundle
        pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius phaseRead →
          Cont phaseRead mesh compactRead →
            Cont compactRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                PkgSig bundle uniformRead pkg →
                  UnaryHistory auditRead ∧
                    UnaryHistory phaseRead ∧
                      UnaryHistory compactRead ∧
                        UnaryHistory continuousRead ∧
                          UnaryHistory uniformRead ∧
                            Cont route nameRow auditRead ∧
                              Cont auditRead radius phaseRead ∧
                                Cont phaseRead mesh compactRead ∧
                                  Cont compactRead route continuousRead ∧
                                    Cont continuousRead nameRow uniformRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle uniformRead pkg ∧
                                          SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row uniformRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row auditRead ∨ hsame row phaseRead ∨
                                                hsame row compactRead ∨
                                                  hsame row continuousRead ∨
                                                    hsame row uniformRead)
                                            (fun row : BHist =>
                                              hsame row uniformRead ∧
                                                PkgSig bundle uniformRead pkg)
                                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeAudit auditPhase phaseCompact compactContinuous continuousUniform
    uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditPhase
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed phaseUnary meshUnary phaseCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row auditRead ∨ hsame row phaseRead ∨ hsame row compactRead ∨
            hsame row continuousRead ∨ hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨auditUnary, phaseUnary, compactUnary, continuousUnary, uniformUnary, routeAudit,
      auditPhase, phaseCompact, compactContinuous, continuousUniform, provenancePkg,
      uniformPkg, cert⟩

theorem FiniteLebesgueNumberPhaseRealAuditLedgerSource [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow bundle
        pkg ->
      Cont route nameRow auditRead ->
        Cont auditRead radius phaseRead ->
          PkgSig bundle phaseRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row auditRead ∨ hsame row phaseRead)
                (fun row : BHist => hsame row phaseRead ∧ PkgSig bundle phaseRead pkg)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory phaseRead ∧
                Cont route nameRow auditRead ∧ Cont auditRead radius phaseRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle phaseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeAudit auditPhase phasePkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditPhase
  have sourcePhase :
      (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row) phaseRead := by
    exact ⟨hsame_refl phaseRead, phaseUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row auditRead ∨ hsame row phaseRead)
        (fun row : BHist => hsame row phaseRead ∧ PkgSig bundle phaseRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro phaseRead sourcePhase
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
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, phasePkg⟩
    }
  exact
    ⟨cert, auditUnary, phaseUnary, routeAudit, auditPhase, provenancePkg, phasePkg⟩

theorem FiniteLebesgueNumberPhaseRealAuditLedgerRootNamecertUse [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead compactRead
      continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow bundle
        pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius phaseRead →
          Cont phaseRead mesh compactRead →
            Cont compactRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                PkgSig bundle auditRead pkg →
                  PkgSig bundle uniformRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          FiniteLebesgueNumberCarrier cover window radius mesh transport route
                              provenance nameRow bundle pkg ∧
                            hsame row nameRow)
                        (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
                        (fun row : BHist =>
                          PkgSig bundle provenance pkg ∧ hsame row nameRow ∧
                            Cont route nameRow auditRead)
                        hsame ∧
                      UnaryHistory auditRead ∧
                        UnaryHistory phaseRead ∧
                          UnaryHistory compactRead ∧
                            UnaryHistory continuousRead ∧
                              UnaryHistory uniformRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle auditRead pkg ∧
                                    PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert Cont hsame
  intro carrier routeAudit auditPhase phaseCompact compactContinuous continuousUniform
    auditPkg uniformPkg
  have rootObligations :=
    FiniteLebesgueNumberCarrier_namecert_obligations
      (cover := cover) (window := window) (radius := radius) (mesh := mesh)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (auditRead := auditRead) (bundle := bundle) (pkg := pkg)
      carrier routeAudit auditPkg
  have phaseReadiness :=
    FiniteLebesgueNumberPhaseRealAuditLedgerReadiness
      (cover := cover) (window := window) (radius := radius) (mesh := mesh)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (auditRead := auditRead) (phaseRead := phaseRead)
      (compactRead := compactRead) (continuousRead := continuousRead)
      (uniformRead := uniformRead) (bundle := bundle) (pkg := pkg) carrier routeAudit
      auditPhase phaseCompact compactContinuous continuousUniform uniformPkg
  obtain ⟨rootCert, _coverUnary, _windowUnary, _radiusUnary, _meshUnary, auditUnary,
    _coverWindowRadius, _radiusMeshRoute, _routeAudit, provenancePkg, auditPkgOut⟩ :=
      rootObligations
  obtain ⟨_auditUnary, phaseUnary, compactUnary, continuousUnary, uniformUnary,
    _routeAuditReady, _auditPhase, _phaseCompact, _compactContinuous, _continuousUniform,
    _provenancePkgReady, uniformPkgOut, _phaseCert⟩ := phaseReadiness
  exact
    ⟨rootCert, auditUnary, phaseUnary, compactUnary, continuousUnary, uniformUnary,
      provenancePkg, auditPkgOut, uniformPkgOut⟩

theorem FiniteLebesgueNumberPhaseRealRadiusAuditClassifier [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead compactRead
      continuousRead uniformRead auditRead' phaseRead' compactRead' continuousRead'
      uniformRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius phaseRead →
          Cont phaseRead mesh compactRead →
            Cont compactRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                Cont route nameRow auditRead' →
                  Cont auditRead' radius phaseRead' →
                    Cont phaseRead' mesh compactRead' →
                      Cont compactRead' route continuousRead' →
                        Cont continuousRead' nameRow uniformRead' →
                          hsame uniformRead uniformRead' →
                            PkgSig bundle uniformRead pkg →
                              PkgSig bundle uniformRead' pkg →
                                UnaryHistory uniformRead ∧ UnaryHistory uniformRead' ∧
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row uniformRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row auditRead ∨ hsame row phaseRead ∨
                                        hsame row compactRead ∨ hsame row continuousRead ∨
                                          hsame row uniformRead)
                                    (fun row : BHist =>
                                      hsame row uniformRead ∧
                                        PkgSig bundle uniformRead pkg)
                                    hsame ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row uniformRead' ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row auditRead' ∨ hsame row phaseRead' ∨
                                          hsame row compactRead' ∨
                                            hsame row continuousRead' ∨
                                              hsame row uniformRead')
                                      (fun row : BHist =>
                                        hsame row uniformRead' ∧
                                          PkgSig bundle uniformRead' pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeAudit auditPhase phaseCompact compactContinuous continuousUniform
    routeAudit' auditPhase' phaseCompact' compactContinuous' continuousUniform'
    _sameUniform uniformPkg uniformPkg'
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditPhase
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed phaseUnary meshUnary phaseCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousUniform
  have auditUnary' : UnaryHistory auditRead' :=
    unary_cont_closed routeUnary nameRowUnary routeAudit'
  have phaseUnary' : UnaryHistory phaseRead' :=
    unary_cont_closed auditUnary' radiusUnary auditPhase'
  have compactUnary' : UnaryHistory compactRead' :=
    unary_cont_closed phaseUnary' meshUnary phaseCompact'
  have continuousUnary' : UnaryHistory continuousRead' :=
    unary_cont_closed compactUnary' routeUnary compactContinuous'
  have uniformUnary' : UnaryHistory uniformRead' :=
    unary_cont_closed continuousUnary' nameRowUnary continuousUniform'
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have sourceUniform' :
      (fun row : BHist => hsame row uniformRead' ∧ UnaryHistory row) uniformRead' := by
    exact ⟨hsame_refl uniformRead', uniformUnary'⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row auditRead ∨ hsame row phaseRead ∨ hsame row compactRead ∨
            hsame row continuousRead ∨ hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  have cert' :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead' ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row auditRead' ∨ hsame row phaseRead' ∨ hsame row compactRead' ∨
            hsame row continuousRead' ∨ hsame row uniformRead')
        (fun row : BHist => hsame row uniformRead' ∧ PkgSig bundle uniformRead' pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead' sourceUniform'
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg'⟩
    }
  exact ⟨uniformUnary, uniformUnary', cert, cert'⟩

theorem FiniteLebesgueNumberPhaseRealAuditLedgerScope [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead compactRead
      continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow bundle
        pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius phaseRead →
          Cont phaseRead mesh compactRead →
            Cont compactRead route continuousRead →
              Cont continuousRead nameRow uniformRead →
                PkgSig bundle uniformRead pkg →
                  UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                    UnaryHistory mesh ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                      UnaryHistory provenance ∧ UnaryHistory nameRow ∧
                        UnaryHistory auditRead ∧ UnaryHistory phaseRead ∧
                          UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                            UnaryHistory uniformRead ∧ Cont route nameRow auditRead ∧
                              Cont auditRead radius phaseRead ∧
                                Cont phaseRead mesh compactRead ∧
                                  Cont compactRead route continuousRead ∧
                                    Cont continuousRead nameRow uniformRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeAudit auditPhase phaseCompact compactContinuous continuousUniform
    uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditPhase
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed phaseUnary meshUnary phaseCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousUniform
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, auditUnary, phaseUnary, compactUnary,
      continuousUnary, uniformUnary, routeAudit, auditPhase, phaseCompact,
      compactContinuous, continuousUniform, provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberPhaseRealRadiusAuditNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow auditRead phaseRead
      terminalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance
        nameRow bundle pkg →
      Cont route nameRow auditRead →
        Cont auditRead radius phaseRead →
          Cont phaseRead mesh terminalRead →
            PkgSig bundle terminalRead pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row auditRead ∨ hsame row phaseRead ∨
                        hsame row terminalRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg ∧
                        hsame row terminalRead)
                    hsame ∧
                UnaryHistory terminalRead ∧
                  (Cont terminalRead (BHist.e0 hostTail) phaseRead → False) ∧
                    (Cont terminalRead (BHist.e1 hostTail) phaseRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeAudit auditPhase phaseTerminal terminalPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routeUnary nameRowUnary routeAudit
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed auditUnary radiusUnary auditPhase
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed phaseUnary meshUnary phaseTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row auditRead ∨ hsame row phaseRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg ∧
              hsame row terminalRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro terminalRead sourceTerminal
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
        exact ⟨provenancePkg, terminalPkg, source.left⟩
    }
  have noZeroTail : Cont terminalRead (BHist.e0 hostTail) phaseRead → False := by
    intro back
    exact cont_mutual_extension_right_tail_absurd.left phaseTerminal back
  have noOneTail : Cont terminalRead (BHist.e1 hostTail) phaseRead → False := by
    intro back
    exact cont_mutual_extension_right_tail_absurd.right phaseTerminal back
  exact ⟨cert, terminalUnary, noZeroTail, noOneTail⟩

end BEDC.Derived.FiniteLebesgueNumberUp
