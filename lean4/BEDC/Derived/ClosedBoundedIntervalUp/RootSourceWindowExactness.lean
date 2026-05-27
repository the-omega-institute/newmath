import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_source_window_exactness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported windowRead windowSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont rational dyadic windowRead ->
        Cont windowRead readback windowSeal ->
          PkgSig bundle windowSeal pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory rational ∧
              UnaryHistory dyadic ∧ UnaryHistory windowRead ∧ UnaryHistory windowSeal ∧
                Cont rational dyadic windowRead ∧ Cont windowRead readback windowSeal ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle windowSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet windowRoute sealRoute windowSealPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, rationalUnary, dyadicUnary, _streamUnary,
    readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _carrierSealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary dyadicUnary windowRoute
  have windowSealUnary : UnaryHistory windowSeal :=
    unary_cont_closed windowReadUnary readbackUnary sealRoute
  exact
    ⟨lowerUnary, upperUnary, rationalUnary, dyadicUnary, windowReadUnary, windowSealUnary,
      windowRoute, sealRoute, provenancePkg, windowSealPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
