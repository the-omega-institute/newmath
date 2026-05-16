import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_provenance_route_exhaustion [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow provenanceRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont route provenance provenanceRead →
        PkgSig bundle provenanceRead pkg →
          UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
            UnaryHistory readback ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
              UnaryHistory provenanceRead ∧ Cont socket question readback ∧
                Cont question refusal route ∧ Cont route provenance provenanceRead ∧
                  hsame readback (append socket question) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle provenanceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier provenanceRoute provenanceReadPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed routeUnary provenanceUnary provenanceRoute
  exact
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, routeUnary, provenanceUnary,
      provenanceReadUnary, socketQuestionReadback, questionRefusalRoute, provenanceRoute,
      readbackSameSourceQuestion, provenancePkg, provenanceReadPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
