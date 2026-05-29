import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_source_dependency_scope [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported intervalNet locatedCover nestedWindow uniformWindow prefixOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont dyadic stream intervalNet →
        Cont rational dyadic locatedCover →
          Cont intervalNet sealRow nestedWindow →
            Cont nestedWindow readback uniformWindow →
              Cont uniformWindow provenance prefixOut →
                PkgSig bundle prefixOut pkg →
                  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rational ∧
                    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
                      UnaryHistory sealRow ∧ UnaryHistory intervalNet ∧
                        UnaryHistory locatedCover ∧ UnaryHistory nestedWindow ∧
                          UnaryHistory uniformWindow ∧ UnaryHistory prefixOut ∧
                            Cont dyadic stream intervalNet ∧
                              Cont rational dyadic locatedCover ∧
                                Cont intervalNet sealRow nestedWindow ∧
                                  Cont nestedWindow readback uniformWindow ∧
                                    Cont uniformWindow provenance prefixOut ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle prefixOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet intervalRoute locatedRoute nestedRoute uniformRoute prefixRoute prefixPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have intervalNetUnary : UnaryHistory intervalNet :=
    unary_cont_closed dyadicUnary streamUnary intervalRoute
  have locatedCoverUnary : UnaryHistory locatedCover :=
    unary_cont_closed rationalUnary dyadicUnary locatedRoute
  have nestedWindowUnary : UnaryHistory nestedWindow :=
    unary_cont_closed intervalNetUnary sealRowUnary nestedRoute
  have uniformWindowUnary : UnaryHistory uniformWindow :=
    unary_cont_closed nestedWindowUnary readbackUnary uniformRoute
  have prefixOutUnary : UnaryHistory prefixOut :=
    unary_cont_closed uniformWindowUnary provenanceUnary prefixRoute
  exact
    ⟨lowerUnary, upperUnary, rationalUnary, dyadicUnary, streamUnary, readbackUnary,
      sealRowUnary, intervalNetUnary, locatedCoverUnary, nestedWindowUnary,
      uniformWindowUnary, prefixOutUnary, intervalRoute, locatedRoute, nestedRoute,
      uniformRoute, prefixRoute, provenancePkg, prefixPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
