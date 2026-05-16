import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_readback_route [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route rootRead →
        PkgSig bundle rootRead pkg →
          UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
            UnaryHistory readback ∧ UnaryHistory rootRead ∧
              Cont socket question readback ∧ Cont question refusal route ∧
                Cont readback route rootRead ∧ hsame readback (append socket question) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier readbackRouteRoot rootPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteRoot
  exact
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, rootUnary,
      socketQuestionReadback, questionRefusalRoute, readbackRouteRoot,
      readbackSameSourceQuestion, provenancePkg, rootPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
