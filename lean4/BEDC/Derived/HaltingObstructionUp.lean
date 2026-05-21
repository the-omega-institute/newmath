import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HaltingObstructionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem HaltingObstructionTraceCoverage [AskSetup] [PackageSetup]
    {cert input trace self policy transport route provenance name traceRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingObstructionCarrier cert input trace self policy transport route provenance name
        bundle pkg →
      Cont trace transport traceRead →
        Cont traceRead policy endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory traceRead ∧ UnaryHistory endpoint ∧ Cont trace transport traceRead ∧
              Cont traceRead policy endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier traceTransportRead readPolicyEndpoint endpointPkg
  obtain ⟨_certUnary, _inputUnary, traceUnary, _selfUnary, policyUnary, transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, _certInputTrace, _traceSelfRoute,
    _routePolicyName, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary transportUnary traceTransportRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceReadUnary policyUnary readPolicyEndpoint
  exact
    ⟨traceReadUnary, endpointUnary, traceTransportRead, readPolicyEndpoint, provenancePkg,
      endpointPkg⟩

theorem HaltingObstructionSelfReferenceRouteDeterminacy [AskSetup] [PackageSetup]
    {cert input trace self policy transport route provenance name selfRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingObstructionCarrier cert input trace self policy transport route provenance name
        bundle pkg →
      Cont input trace selfRead →
        Cont selfRead self endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory selfRead ∧ UnaryHistory endpoint ∧ Cont cert input trace ∧
              Cont input trace selfRead ∧ Cont selfRead self endpoint ∧
                Cont trace self route ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier inputTraceRead readSelfEndpoint endpointPkg
  obtain ⟨_certUnary, inputUnary, traceUnary, selfUnary, _policyUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, certInputTrace, traceSelfRoute,
    _routePolicyName, provenancePkg⟩ := carrier
  have selfReadUnary : UnaryHistory selfRead :=
    unary_cont_closed inputUnary traceUnary inputTraceRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed selfReadUnary selfUnary readSelfEndpoint
  exact
    ⟨selfReadUnary, endpointUnary, certInputTrace, inputTraceRead, readSelfEndpoint,
      traceSelfRoute, provenancePkg, endpointPkg⟩

theorem HaltingObstructionNamecertObligations [AskSetup] [PackageSetup]
    {cert input trace self policy transport route provenance name replay endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingObstructionCarrier cert input trace self policy transport route provenance name
        bundle pkg →
      Cont trace self replay →
        Cont replay policy endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                (fun row : BHist => hsame row endpoint)
                (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                hsame ∧
              UnaryHistory cert ∧ UnaryHistory input ∧ UnaryHistory trace ∧
                UnaryHistory self ∧ UnaryHistory policy ∧ UnaryHistory transport ∧
                  UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                    UnaryHistory replay ∧ UnaryHistory endpoint ∧
                      Cont cert input trace ∧ Cont trace self route ∧
                        Cont route policy name ∧ Cont trace self replay ∧
                          Cont replay policy endpoint ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier traceSelfReplay replayPolicyEndpoint endpointPkg
  obtain ⟨certUnary, inputUnary, traceUnary, selfUnary, policyUnary, transportUnary,
    routeUnary, provenanceUnary, nameUnary, certInputTrace, traceSelfRoute,
    routePolicyName, provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed traceUnary selfUnary traceSelfReplay
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary policyUnary replayPolicyEndpoint
  have sourceAtEndpoint : hsame endpoint endpoint ∧ UnaryHistory endpoint :=
    ⟨hsame_refl endpoint, endpointUnary⟩
  have certSurface :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }
  exact
    ⟨certSurface, certUnary, inputUnary, traceUnary, selfUnary, policyUnary, transportUnary,
      routeUnary, provenanceUnary, nameUnary, replayUnary, endpointUnary, certInputTrace,
      traceSelfRoute, routePolicyName, traceSelfReplay, replayPolicyEndpoint, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.HaltingObstructionUp
