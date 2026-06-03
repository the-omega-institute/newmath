import BEDC.Derived.CannotClaimExportGateUp.TasteGate

namespace BEDC.Derived.CannotClaimExportGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CannotClaimExportGateUp
