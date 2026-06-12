import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_mature_consumer_surface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead coverRead compactRead publicRead finiteCoverRead locatedCoverRead
      modulusRead matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported dyadic netRead ->
        Cont exported stream coverRead ->
          Cont netRead coverRead compactRead ->
            Cont exported localName publicRead ->
              Cont publicRead dyadic finiteCoverRead ->
                Cont finiteCoverRead stream locatedCoverRead ->
                  Cont locatedCoverRead sealRow modulusRead ->
                    Cont modulusRead readback matureRead ->
                      PkgSig bundle compactRead pkg ->
                        PkgSig bundle matureRead pkg ->
                          UnaryHistory netRead ∧ UnaryHistory coverRead ∧
                            UnaryHistory compactRead ∧ UnaryHistory publicRead ∧
                              UnaryHistory finiteCoverRead ∧ UnaryHistory locatedCoverRead ∧
                                UnaryHistory modulusRead ∧ UnaryHistory matureRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg ∧
                                      PkgSig bundle compactRead pkg ∧
                                        PkgSig bundle matureRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet exportedDyadicNet exportedStreamCover netCoverCompact publicRoute finiteRoute
    locatedRoute modulusRoute matureRoute compactPkg maturePkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _transportRoute, _exportRoute, provenancePkg, localNamePkg⟩ := packet
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed exportedUnary dyadicUnary exportedDyadicNet
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed exportedUnary streamUnary exportedStreamCover
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed netReadUnary coverReadUnary netCoverCompact
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed exportedUnary localNameUnary publicRoute
  have finiteCoverReadUnary : UnaryHistory finiteCoverRead :=
    unary_cont_closed publicReadUnary dyadicUnary finiteRoute
  have locatedCoverReadUnary : UnaryHistory locatedCoverRead :=
    unary_cont_closed finiteCoverReadUnary streamUnary locatedRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed locatedCoverReadUnary sealRowUnary modulusRoute
  have matureReadUnary : UnaryHistory matureRead :=
    unary_cont_closed modulusReadUnary readbackUnary matureRoute
  exact
    ⟨netReadUnary, coverReadUnary, compactReadUnary, publicReadUnary, finiteCoverReadUnary,
      locatedCoverReadUnary, modulusReadUnary, matureReadUnary, provenancePkg, localNamePkg,
      compactPkg, maturePkg⟩

end BEDC.Derived.ClosedboundedintervalUp
