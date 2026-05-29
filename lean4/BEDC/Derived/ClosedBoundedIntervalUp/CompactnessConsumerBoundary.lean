import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_compactness_consumer_boundary [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteNet locatedCover nestedRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream finiteNet ->
        Cont finiteNet readback locatedCover ->
          Cont locatedCover sealRow nestedRead ->
            Cont nestedRead provenance compactRead ->
              PkgSig bundle compactRead pkg ->
                UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
                  UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory finiteNet ∧
                    UnaryHistory locatedCover ∧ UnaryHistory nestedRead ∧
                      UnaryHistory compactRead ∧ Cont dyadic stream finiteNet ∧
                        Cont finiteNet readback locatedCover ∧
                          Cont locatedCover sealRow nestedRead ∧
                            Cont nestedRead provenance compactRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                                PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet dyadicStreamFinite finiteReadbackLocated locatedSealNested nestedProvenanceCompact
    compactPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamFinite
  have locatedCoverUnary : UnaryHistory locatedCover :=
    unary_cont_closed finiteNetUnary readbackUnary finiteReadbackLocated
  have nestedReadUnary : UnaryHistory nestedRead :=
    unary_cont_closed locatedCoverUnary sealRowUnary locatedSealNested
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed nestedReadUnary provenanceUnary nestedProvenanceCompact
  exact
    ⟨dyadicUnary, streamUnary, readbackUnary, sealRowUnary, provenanceUnary, finiteNetUnary,
      locatedCoverUnary, nestedReadUnary, compactReadUnary, dyadicStreamFinite,
      finiteReadbackLocated, locatedSealNested, nestedProvenanceCompact, provenancePkg,
      localNamePkg, compactPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
