import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_source_scope_package [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteCover nestedWindow uniformWindow completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream finiteCover ->
        Cont finiteCover sealRow nestedWindow ->
          Cont nestedWindow readback uniformWindow ->
            Cont uniformWindow provenance completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory dyadic ∧
                  UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                    UnaryHistory finiteCover ∧ UnaryHistory nestedWindow ∧
                      UnaryHistory uniformWindow ∧ UnaryHistory completionRead ∧
                        Cont dyadic stream finiteCover ∧
                          Cont finiteCover sealRow nestedWindow ∧
                            Cont nestedWindow readback uniformWindow ∧
                              Cont uniformWindow provenance completionRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet dyadicStreamCover coverSealNested nestedReadbackUniform
  intro uniformProvenanceCompletion completionPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have finiteCoverUnary : UnaryHistory finiteCover :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamCover
  have nestedWindowUnary : UnaryHistory nestedWindow :=
    unary_cont_closed finiteCoverUnary sealRowUnary coverSealNested
  have uniformWindowUnary : UnaryHistory uniformWindow :=
    unary_cont_closed nestedWindowUnary readbackUnary nestedReadbackUniform
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed uniformWindowUnary provenanceUnary uniformProvenanceCompletion
  exact
    ⟨lowerUnary, upperUnary, dyadicUnary, streamUnary, readbackUnary, sealRowUnary,
      finiteCoverUnary, nestedWindowUnary, uniformWindowUnary, completionUnary,
      dyadicStreamCover, coverSealNested, nestedReadbackUniform, uniformProvenanceCompletion,
      provenancePkg, completionPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
