import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_cauchy_source_route_scope [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance sourceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont source handoff sourceRead ->
        Cont sourceRead separated sealRead ->
          PkgSig bundle sourceRead pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory sourceRead ∧ UnaryHistory sealRead ∧
                Cont source entourage transport ∧ Cont source handoff sourceRead ∧
                  Cont sourceRead separated sealRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sourceRead pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier sourceHandoffRead readSeparatedSeal sourceReadPkg sealReadPkg
  obtain ⟨sourceUnary, _entourageUnary, separatedUnary, handoffUnary, _transportUnary,
    _routeUnary, _provenanceUnary, sourceEntourageTransport, _separatedHandoffRoute,
    _transportRouteProvenance, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary handoffUnary sourceHandoffRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceReadUnary separatedUnary readSeparatedSeal
  exact
    ⟨sourceReadUnary, sealReadUnary, sourceEntourageTransport, sourceHandoffRead,
      readSeparatedSeal, provenancePkg, sourceReadPkg, sealReadPkg⟩

end BEDC.Derived.HausdorffCompletionUp
