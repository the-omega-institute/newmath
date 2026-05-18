import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_zero_consumer_source_readiness
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' sourceRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont transports' routes provenance' ->
            Cont pole zeroLedger' gamma' ->
              PkgSig bundle provenance' pkg ->
                hsame eta eta' ->
                  hsame zeroLedger zeroLedger' ->
                    UnaryHistory routes ->
                      UnaryHistory name ->
                        Cont routes name sourceRead ->
                          Cont routes name zeroRead ->
                            PkgSig bundle zeroRead pkg ->
                              hsame analytic analytic' ∧ hsame transports transports' ∧
                                hsame provenance provenance' ∧ hsame gamma gamma' ∧
                                  hsame sourceRead zeroRead ∧ UnaryHistory sourceRead ∧
                                    UnaryHistory zeroRead ∧
                                      hsame sourceRead (append routes name) ∧
                                        hsame zeroRead (append routes name) ∧
                                          PkgSig bundle name pkg ∧
                                            PkgSig bundle provenance' pkg ∧
                                              PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary sourceRoute zeroRoute zeroPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := sourceRead)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary sourceRoute
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, sourceUnary,
    sourceSame, namePkg, provenancePkg'⟩ := readiness
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed routesUnary nameUnary zeroRoute
  have zeroSame : hsame zeroRead (append routes name) :=
    zeroRoute
  have readsSame : hsame sourceRead zeroRead :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) sourceRoute zeroRoute
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, readsSame, sourceUnary,
      zeroUnary, sourceSame, zeroSame, namePkg, provenancePkg', zeroPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
