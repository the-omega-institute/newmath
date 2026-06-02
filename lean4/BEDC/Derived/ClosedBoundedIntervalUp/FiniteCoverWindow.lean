import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalFiniteCoverWindow [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported coverWindow coverReadback coverSeal : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
      transport replay provenance localName exported bundle pkg ∧
    Cont dyadic stream coverWindow ∧ Cont coverWindow readback coverReadback ∧
      Cont coverReadback sealRow coverSeal ∧ PkgSig bundle coverSeal pkg

theorem ClosedBoundedIntervalFiniteCoverWindow_carrier_surface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported coverWindow coverReadback coverSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalFiniteCoverWindow lower upper order rational dyadic stream readback
        sealRow transport replay provenance localName exported coverWindow coverReadback
        coverSeal bundle pkg →
      UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
        UnaryHistory sealRow ∧ UnaryHistory coverWindow ∧ UnaryHistory coverReadback ∧
          UnaryHistory coverSeal ∧ Cont dyadic stream coverWindow ∧
            Cont coverWindow readback coverReadback ∧
              Cont coverReadback sealRow coverSeal ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle coverSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro window
  obtain ⟨packet, dyadicStreamWindow, windowReadback, readbackSeal, coverSealPkg⟩ := window
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have coverWindowUnary : UnaryHistory coverWindow :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamWindow
  have coverReadbackUnary : UnaryHistory coverReadback :=
    unary_cont_closed coverWindowUnary readbackUnary windowReadback
  have coverSealUnary : UnaryHistory coverSeal :=
    unary_cont_closed coverReadbackUnary sealRowUnary readbackSeal
  exact
    ⟨dyadicUnary, streamUnary, readbackUnary, sealRowUnary, coverWindowUnary,
      coverReadbackUnary, coverSealUnary, dyadicStreamWindow, windowReadback, readbackSeal,
      provenancePkg, localNamePkg, coverSealPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
