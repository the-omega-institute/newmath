import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_consumer_completeness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead coverRead modulusRead compactRead windowRead windowOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory netRead ->
        Cont dyadic netRead coverRead ->
          Cont sealRow coverRead modulusRead ->
            Cont coverRead sealRow compactRead ->
              Cont stream readback windowRead ->
                Cont windowRead provenance windowOut ->
                  PkgSig bundle modulusRead pkg ->
                    PkgSig bundle compactRead pkg ->
                      PkgSig bundle windowOut pkg ->
                        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory dyadic ∧
                          UnaryHistory sealRow ∧ UnaryHistory coverRead ∧
                            UnaryHistory modulusRead ∧ UnaryHistory compactRead ∧
                              UnaryHistory windowOut ∧ Cont dyadic netRead coverRead ∧
                                Cont sealRow coverRead modulusRead ∧
                                  Cont coverRead sealRow compactRead ∧
                                    Cont stream readback windowRead ∧
                                      Cont windowRead provenance windowOut ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle modulusRead pkg ∧
                                            PkgSig bundle compactRead pkg ∧
                                              PkgSig bundle windowOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet netReadUnary coverRoute modulusRoute compactRoute windowRoute windowOutRoute
    modulusPkg compactPkg windowOutPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed dyadicUnary netReadUnary coverRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sealRowUnary coverReadUnary modulusRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed coverReadUnary sealRowUnary compactRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have windowOutUnary : UnaryHistory windowOut :=
    unary_cont_closed windowReadUnary provenanceUnary windowOutRoute
  exact
    ⟨lowerUnary, upperUnary, dyadicUnary, sealRowUnary, coverReadUnary,
      modulusReadUnary, compactReadUnary, windowOutUnary, coverRoute, modulusRoute,
      compactRoute, windowRoute, windowOutRoute, provenancePkg, modulusPkg, compactPkg,
      windowOutPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
