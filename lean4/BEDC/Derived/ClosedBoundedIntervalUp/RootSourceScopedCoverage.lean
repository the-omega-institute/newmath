import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_source_scoped_coverage [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteCover nestedWindow uniformWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream finiteCover ->
        Cont finiteCover sealRow nestedWindow ->
          Cont nestedWindow readback uniformWindow ->
            PkgSig bundle finiteCover pkg ->
              PkgSig bundle nestedWindow pkg ->
                PkgSig bundle uniformWindow pkg ->
                  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
                    UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                      UnaryHistory readback ∧ UnaryHistory sealRow ∧
                        UnaryHistory finiteCover ∧ UnaryHistory nestedWindow ∧
                          UnaryHistory uniformWindow ∧ Cont dyadic stream finiteCover ∧
                            Cont finiteCover sealRow nestedWindow ∧
                              Cont nestedWindow readback uniformWindow ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle finiteCover pkg ∧
                                    PkgSig bundle nestedWindow pkg ∧
                                      PkgSig bundle uniformWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet finiteCoverRoute nestedWindowRoute uniformWindowRoute finiteCoverPkg
    nestedWindowPkg uniformWindowPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have finiteCoverUnary : UnaryHistory finiteCover :=
    unary_cont_closed dyadicUnary streamUnary finiteCoverRoute
  have nestedWindowUnary : UnaryHistory nestedWindow :=
    unary_cont_closed finiteCoverUnary sealRowUnary nestedWindowRoute
  have uniformWindowUnary : UnaryHistory uniformWindow :=
    unary_cont_closed nestedWindowUnary readbackUnary uniformWindowRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, finiteCoverUnary, nestedWindowUnary, uniformWindowUnary,
      finiteCoverRoute, nestedWindowRoute, uniformWindowRoute, provenancePkg, finiteCoverPkg,
      nestedWindowPkg, uniformWindowPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
