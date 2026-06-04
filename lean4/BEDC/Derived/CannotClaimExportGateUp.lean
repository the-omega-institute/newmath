import BEDC.Derived.CannotClaimExportGateUp.TasteGate

namespace BEDC.Derived.CannotClaimExportGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CannotClaimExportGate_export_grade_scope [AskSetup] [PackageSetup]
    {registry refusal exportDecision exportGrade target audit transport continuation
      provenance name gradeRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CannotClaimExportGateCarrier registry refusal exportDecision exportGrade target audit
        transport continuation provenance name bundle pkg →
      Cont refusal exportDecision gradeRead →
        Cont gradeRead target auditRead →
          PkgSig bundle auditRead pkg →
            UnaryHistory refusal ∧ UnaryHistory exportDecision ∧ UnaryHistory target ∧
              UnaryHistory audit ∧ UnaryHistory gradeRead ∧ UnaryHistory auditRead ∧
                Cont refusal exportDecision gradeRead ∧ Cont gradeRead target auditRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier gradeRoute auditRoute auditPkg
  obtain ⟨_registryUnary, refusalUnary, exportDecisionUnary, _exportGradeUnary,
    targetUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _nameUnary, _registryDecision, _decisionTarget, _targetContinuation,
    _auditProvenance, provenancePkg, namePkg⟩ := carrier
  have gradeReadUnary : UnaryHistory gradeRead :=
    unary_cont_closed refusalUnary exportDecisionUnary gradeRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed gradeReadUnary targetUnary auditRoute
  exact
    ⟨refusalUnary, exportDecisionUnary, targetUnary, auditUnary, gradeReadUnary,
      auditReadUnary, gradeRoute, auditRoute, provenancePkg, namePkg, auditPkg⟩

theorem CannotClaimExportGate_ledger_exhaustion [AskSetup] [PackageSetup]
    {registry refusal exportDecision exportGrade target audit transport continuation
      provenance name route gradeRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CannotClaimExportGateCarrier registry refusal exportDecision exportGrade target audit
        transport continuation provenance name bundle pkg →
      Cont audit transport route →
        Cont refusal exportDecision gradeRead →
          Cont gradeRead target auditRead →
            PkgSig bundle route pkg →
              PkgSig bundle auditRead pkg →
                UnaryHistory registry ∧ UnaryHistory refusal ∧
                  UnaryHistory exportDecision ∧ UnaryHistory exportGrade ∧
                    UnaryHistory target ∧ UnaryHistory audit ∧ UnaryHistory transport ∧
                      UnaryHistory continuation ∧ UnaryHistory provenance ∧
                        UnaryHistory name ∧ UnaryHistory route ∧
                          UnaryHistory gradeRead ∧ UnaryHistory auditRead ∧
                            Cont registry refusal exportDecision ∧
                              Cont exportDecision exportGrade target ∧
                                Cont target audit continuation ∧
                                  Cont audit transport route ∧
                                    Cont refusal exportDecision gradeRead ∧
                                      Cont gradeRead target auditRead ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle name pkg ∧
                                            PkgSig bundle route pkg ∧
                                              PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier auditTransportRoute gradeRoute auditRoute routePkg auditPkg
  obtain ⟨registryUnary, refusalUnary, exportDecisionUnary, exportGradeUnary,
    targetUnary, auditUnary, transportUnary, continuationUnary, provenanceUnary,
    nameUnary, registryRefusalDecision, decisionGradeTarget, targetAuditContinuation,
    _auditTransportProvenance, provenancePkg, namePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed auditUnary transportUnary auditTransportRoute
  have gradeReadUnary : UnaryHistory gradeRead :=
    unary_cont_closed refusalUnary exportDecisionUnary gradeRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed gradeReadUnary targetUnary auditRoute
  exact
    ⟨registryUnary, refusalUnary, exportDecisionUnary, exportGradeUnary, targetUnary,
      auditUnary, transportUnary, continuationUnary, provenanceUnary, nameUnary,
      routeUnary, gradeReadUnary, auditReadUnary, registryRefusalDecision,
      decisionGradeTarget, targetAuditContinuation, auditTransportRoute, gradeRoute,
      auditRoute, provenancePkg, namePkg, routePkg, auditPkg⟩

theorem CannotClaimExportGate_obligation_closure_package [AskSetup] [PackageSetup]
    {registry refusal exportDecision exportGrade target audit transport continuation
      provenance name route gradeRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CannotClaimExportGateCarrier registry refusal exportDecision exportGrade target audit
        transport continuation provenance name bundle pkg →
      Cont audit transport route →
        Cont refusal exportDecision gradeRead →
          Cont gradeRead target auditRead →
            PkgSig bundle route pkg →
              PkgSig bundle auditRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row route ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row registry ∨ hsame row refusal ∨ hsame row exportDecision ∨
                        hsame row exportGrade ∨ hsame row target ∨ hsame row audit ∨
                          hsame row route)
                    (fun _row : BHist => PkgSig bundle route pkg ∧ PkgSig bundle auditRead pkg)
                    hsame ∧
                  UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier auditTransportRoute gradeRoute auditRoute routePkg auditPkg
  obtain ⟨_registryUnary, refusalUnary, exportDecisionUnary, _exportGradeUnary,
    targetUnary, auditUnary, transportUnary, _continuationUnary, _provenanceUnary,
    _nameUnary, _registryDecision, _decisionTarget, _targetContinuation,
    _auditProvenance, _provenancePkg, _namePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed auditUnary transportUnary auditTransportRoute
  have gradeReadUnary : UnaryHistory gradeRead :=
    unary_cont_closed refusalUnary exportDecisionUnary gradeRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed gradeReadUnary targetUnary auditRoute
  have sourceRoute :
      (fun row : BHist => hsame row route ∧ UnaryHistory row) route := by
    exact ⟨hsame_refl route, routeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row route ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row registry ∨ hsame row refusal ∨ hsame row exportDecision ∨
              hsame row exportGrade ∨ hsame row target ∨ hsame row audit ∨
                hsame row route)
          (fun _row : BHist => PkgSig bundle route pkg ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro route sourceRoute
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row _source
      exact ⟨routePkg, auditPkg⟩
  }
  exact ⟨cert, auditReadUnary⟩

end BEDC.Derived.CannotClaimExportGateUp
