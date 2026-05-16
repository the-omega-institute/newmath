import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_socket_refusal_coverage [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route consumerRead →
        PkgSig bundle consumerRead pkg →
          UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
            UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory consumerRead ∧
                Cont socket question readback ∧ Cont question refusal route ∧
                  Cont refusal readback transport ∧ Cont readback route nameRow ∧
                    Cont readback route consumerRead ∧
                      hsame readback (append socket question) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    refusalReadbackTransport, readbackRouteNameRow, readbackSameSourceQuestion,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed readbackUnary routeUnary consumerRoute
  exact
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, consumerUnary, socketQuestionReadback,
      questionRefusalRoute, refusalReadbackTransport, readbackRouteNameRow, consumerRoute,
      readbackSameSourceQuestion, provenancePkg, consumerPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
