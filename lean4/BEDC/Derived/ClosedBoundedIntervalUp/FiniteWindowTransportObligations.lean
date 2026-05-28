import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_finite_window_transport_obligations
    [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported stream' readback' sealRow' transportedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      hsame stream stream' ->
        hsame readback readback' ->
          hsame sealRow sealRow' ->
            Cont stream' readback' transportedWindow ->
              PkgSig bundle transportedWindow pkg ->
                UnaryHistory stream' ∧ UnaryHistory readback' ∧ UnaryHistory sealRow' ∧
                  UnaryHistory transportedWindow ∧ Cont stream' readback' transportedWindow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle transportedWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet sameStream sameReadback sameSealRow transportedRoute transportedPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have transportedStreamUnary : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have transportedReadbackUnary : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have transportedSealRowUnary : UnaryHistory sealRow' :=
    unary_transport sealRowUnary sameSealRow
  have transportedWindowUnary : UnaryHistory transportedWindow :=
    unary_cont_closed transportedStreamUnary transportedReadbackUnary transportedRoute
  exact
    ⟨transportedStreamUnary, transportedReadbackUnary, transportedSealRowUnary,
      transportedWindowUnary, transportedRoute, provenancePkg, localNamePkg, transportedPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
