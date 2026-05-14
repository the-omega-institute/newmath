import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HaltingObstructionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HaltingObstructionCarrier [AskSetup] [PackageSetup]
    (cert input trace self policy transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cert ∧ UnaryHistory input ∧ UnaryHistory trace ∧ UnaryHistory self ∧
    UnaryHistory policy ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont cert input trace ∧
        Cont trace self route ∧ Cont route policy name ∧ PkgSig bundle provenance pkg

theorem HaltingObstructionRootCarrierAdmission [AskSetup] [PackageSetup]
    {cert input trace self policy transport route provenance name replay endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingObstructionCarrier cert input trace self policy transport route provenance name
        bundle pkg →
      Cont trace self replay →
        Cont replay policy endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory replay ∧ UnaryHistory endpoint ∧ Cont trace self replay ∧
              Cont replay policy endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier traceSelfReplay replayPolicyEndpoint endpointPkg
  obtain ⟨_certUnary, _inputUnary, traceUnary, selfUnary, policyUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, _certInputTrace, _traceSelfRoute,
    _routePolicyName, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed traceUnary selfUnary traceSelfReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary policyUnary replayPolicyEndpoint
  exact
    ⟨replayUnary, endpointUnary, traceSelfReplay, replayPolicyEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.HaltingObstructionUp
