import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_public_source_lock_export [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' publicRoot sourceLock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont transports' routes provenance' ->
            PkgSig bundle provenance' pkg ->
              hsame eta eta' ->
                UnaryHistory routes ->
                  UnaryHistory name ->
                    Cont routes name publicRoot ->
                      Cont basic analytic' sourceLock ->
                        PkgSig bundle sourceLock pkg ->
                          hsame analytic analytic' ∧ hsame transports transports' ∧
                            hsame provenance provenance' ∧ UnaryHistory publicRoot ∧
                              hsame publicRoot (append routes name) ∧
                                hsame sourceLock (append basic analytic') ∧
                                  PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg ∧
                                    PkgSig bundle sourceLock pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame routesUnary
    nameUnary routesNamePublic basicAnalyticSource sourceLockPkg
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have publicRootUnary : UnaryHistory publicRoot :=
    unary_cont_closed routesUnary nameUnary routesNamePublic
  exact
    ⟨analyticSame, transportsSame, provenanceSame, publicRootUnary, routesNamePublic,
      basicAnalyticSource, namePkg, provenancePkg', sourceLockPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
