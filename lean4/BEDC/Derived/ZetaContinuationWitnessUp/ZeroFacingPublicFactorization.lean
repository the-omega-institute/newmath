import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_zero_facing_public_factorization [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroRead criticalRead : BHist}
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
                    Cont routes name zeroRead ->
                      Cont routes name criticalRead ->
                        PkgSig bundle zeroRead pkg ->
                          hsame analytic analytic' ∧ hsame transports transports' ∧
                            hsame provenance provenance' ∧ UnaryHistory zeroRead ∧
                              UnaryHistory criticalRead ∧ hsame zeroRead criticalRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg ∧
                                  PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame routesUnary
    nameUnary zeroRoute criticalRoute zeroPkg
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (bundle := bundle)
      (pkg := pkg) packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed routesUnary nameUnary zeroRoute
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary criticalRoute
  have readsSame : hsame zeroRead criticalRead :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) zeroRoute criticalRoute
  exact
    ⟨analyticSame, transportsSame, provenanceSame, zeroUnary, criticalUnary, readsSame,
      namePkg, provenancePkg', zeroPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
