import BEDC.Derived.LipschitzMapUp

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LipschitzMapCarrier_separated_completion_nonescape [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert separatedRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg →
      Cont target transports separatedRead →
        Cont separatedRead routes completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory separatedRead ∧
              UnaryHistory completionRead ∧ Cont target transports separatedRead ∧
                Cont separatedRead routes completionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier separatedRoute completionRoute completionPkg
  obtain ⟨sourceUnary, targetUnary, _boundUnary, _graphUnary, transportsUnary, routesUnary,
    _localCertUnary, _graphBoundModulus, _modulusRoutesProvenance, provenancePkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed targetUnary transportsUnary separatedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary routesUnary completionRoute
  exact
    ⟨sourceUnary, targetUnary, separatedUnary, completionUnary, separatedRoute,
      completionRoute, provenancePkg, completionPkg⟩

end BEDC.Derived.LipschitzMapUp
