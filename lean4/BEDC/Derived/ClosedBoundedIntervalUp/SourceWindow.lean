import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalSourceWindow [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported sourceWindow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory ClosedBoundedIntervalPacket
  BEDC.Derived.ClosedboundedintervalUp.ClosedBoundedIntervalPacket lower upper order rational
      dyadic stream readback sealRow transport replay provenance localName exported bundle pkg ∧
    Cont rational dyadic stream ∧ Cont localName exported sourceWindow

theorem ClosedBoundedIntervalSourceWindow_exactness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported sourceWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalSourceWindow lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported sourceWindow bundle pkg ->
      UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory sourceWindow ∧
        Cont rational dyadic stream ∧ Cont stream readback sealRow ∧
          Cont transport replay provenance ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro window
  obtain ⟨packet, rationalWindow, sourceRoute⟩ := window
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    sealRoute, replayRoute, _nameRoute, _provenancePkg, localNamePkg⟩ := packet
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed localNameUnary exportedUnary sourceRoute
  exact
    ⟨lowerUnary, upperUnary, sourceWindowUnary, rationalWindow, sealRoute, replayRoute,
      localNamePkg⟩

end BEDC.Derived.ClosedBoundedIntervalUp
