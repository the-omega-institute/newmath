import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_kind_readback_determinacy [AskSetup] [PackageSetup]
    {socket question refusal readback readback' transport route provenance nameRow
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question readback' →
        Cont readback' route auditRead →
          PkgSig bundle auditRead pkg →
            hsame readback readback' ∧ hsame readback' (append socket question) ∧
              UnaryHistory auditRead ∧ Cont socket question readback' ∧
                Cont question refusal route ∧ Cont readback' route auditRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier socketQuestionReadback' readbackRouteAudit auditPkg
  obtain ⟨_socketUnary, _questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameAppend, provenancePkg⟩ := carrier
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame (hsame_refl socket) (hsame_refl question) socketQuestionReadback
      socketQuestionReadback'
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary' routeUnary readbackRouteAudit
  have readback'SameAppend : hsame readback' (append socket question) :=
    hsame_trans (hsame_symm sameReadback) readbackSameAppend
  exact
    ⟨sameReadback, readback'SameAppend, auditUnary, socketQuestionReadback',
      questionRefusalRoute, readbackRouteAudit, provenancePkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
