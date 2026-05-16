import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_boundary_row_triad [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow socketRead
      refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question socketRead →
        Cont question refusal refusalRead →
          PkgSig bundle refusalRead pkg →
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
              UnaryHistory socketRead ∧ UnaryHistory refusalRead ∧
                Cont socket question socketRead ∧ Cont question refusal refusalRead ∧
                  hsame readback (append socket question) ∧ PkgSig bundle refusalRead pkg ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier socketQuestionRead refusalReadRoute refusalReadPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, _readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary questionUnary socketQuestionRead
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed questionUnary refusalUnary refusalReadRoute
  exact
    ⟨socketUnary, questionUnary, refusalUnary, socketReadUnary, refusalReadUnary,
      socketQuestionRead, refusalReadRoute, readbackSameSourceQuestion, refusalReadPkg,
      provenancePkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
