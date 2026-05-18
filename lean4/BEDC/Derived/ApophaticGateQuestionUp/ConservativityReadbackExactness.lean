import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_conservativity_readback_exactness
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow conservativityRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback provenance conservativityRead →
        PkgSig bundle conservativityRead pkg →
          UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
            UnaryHistory readback ∧ UnaryHistory conservativityRead ∧
              hsame readback (append socket question) ∧ Cont socket question readback ∧
                Cont question refusal route ∧ Cont refusal readback transport ∧
                  Cont readback provenance conservativityRead ∧
                    PkgSig bundle provenance pkg ∧
                      PkgSig bundle conservativityRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg hsame ProbeBundle UnaryHistory
  intro carrier conservativityRoute conservativityPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have conservativityUnary : UnaryHistory conservativityRead :=
    unary_cont_closed readbackUnary provenanceUnary conservativityRoute
  exact
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, conservativityUnary,
      readbackSameSourceQuestion, socketQuestionReadback, questionRefusalRoute,
      refusalReadbackTransport, conservativityRoute, provenancePkg, conservativityPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
