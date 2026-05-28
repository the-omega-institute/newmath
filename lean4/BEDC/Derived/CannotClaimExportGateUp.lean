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

end BEDC.Derived.CannotClaimExportGateUp
