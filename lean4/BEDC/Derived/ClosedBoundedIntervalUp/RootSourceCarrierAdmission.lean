import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_source_carrier_admission [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported rootSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont lower upper rootSource ->
        PkgSig bundle rootSource pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rootSource ∧
            Cont lower upper rootSource ∧ Cont order rational dyadic ∧
              Cont stream readback sealRow ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle rootSource pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet rootRoute rootPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute, dyadicRoute,
    sealRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have rootUnary : UnaryHistory rootSource :=
    unary_cont_closed lowerUnary upperUnary rootRoute
  exact
    ⟨lowerUnary, upperUnary, rootUnary, rootRoute, dyadicRoute, sealRoute, provenancePkg,
      rootPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
