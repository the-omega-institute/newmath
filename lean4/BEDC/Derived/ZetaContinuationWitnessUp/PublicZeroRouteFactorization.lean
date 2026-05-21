import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPublicZeroRouteFactorization [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      publicRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          UnaryHistory zeroLedger ->
            Cont routes name publicRead ->
              Cont publicRead zeroLedger zeroRead ->
                PkgSig bundle zeroRead pkg ->
                  UnaryHistory publicRead /\ UnaryHistory zeroRead /\
                    hsame publicRead (append routes name) /\
                      Cont publicRead zeroLedger zeroRead /\
                        Cont transports routes provenance /\ PkgSig bundle name pkg /\
                          PkgSig bundle provenance pkg /\ PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary zeroLedgerUnary routesNamePublic publicZeroRead zeroReadPkg
  obtain ⟨_basicAnalytic, _analyticTransport, _poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary routesNamePublic
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed publicUnary zeroLedgerUnary publicZeroRead
  exact
    ⟨publicUnary, zeroUnary, routesNamePublic, publicZeroRead, transportsRoutesProvenance,
      namePkg, provenancePkg, zeroReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
