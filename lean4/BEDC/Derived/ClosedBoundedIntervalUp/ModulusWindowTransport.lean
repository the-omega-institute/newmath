import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_modulus_window_transport [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported modulusWindow modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory modulusWindow ->
        Cont dyadic stream modulusWindow ->
          Cont modulusWindow readback modulusRead ->
            PkgSig bundle modulusRead pkg ->
              UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
                UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
                  UnaryHistory sealRow ∧ UnaryHistory modulusWindow ∧
                    UnaryHistory modulusRead ∧ Cont dyadic stream modulusWindow ∧
                      Cont modulusWindow readback modulusRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                          PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet modulusWindowUnary modulusWindowRoute modulusReadRoute modulusReadPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed modulusWindowUnary readbackUnary modulusReadRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, dyadicUnary, streamUnary, readbackUnary,
      sealRowUnary, modulusWindowUnary, modulusReadUnary, modulusWindowRoute,
      modulusReadRoute, provenancePkg, localNamePkg, modulusReadPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
