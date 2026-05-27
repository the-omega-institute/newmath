import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_finite_cover_nonescape [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported coverWindow coverReadback coverSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg)
    (coverWindowUnary : UnaryHistory coverWindow)
    (coverReadbackUnary : UnaryHistory coverReadback)
    (coverRoute : Cont coverWindow coverReadback coverSeal) :
    UnaryHistory coverSeal ∧ hsame order (append lower upper) ∧
      hsame sealRow (append stream readback) ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, endpointRoute, _containmentRoute,
    sealRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have coverSealUnary : UnaryHistory coverSeal :=
    unary_cont_closed coverWindowUnary coverReadbackUnary coverRoute
  exact ⟨coverSealUnary, endpointRoute, sealRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.ClosedboundedintervalUp
