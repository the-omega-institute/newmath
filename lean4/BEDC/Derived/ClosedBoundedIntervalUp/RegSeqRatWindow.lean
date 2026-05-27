import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_regseqrat_window [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported windowRead windowOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont stream readback windowRead ->
        Cont windowRead provenance windowOut ->
          PkgSig bundle windowOut pkg ->
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory windowRead ∧
              UnaryHistory windowOut ∧ Cont stream readback sealRow ∧
                Cont stream readback windowRead ∧ Cont windowRead provenance windowOut ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle windowOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet windowReadRoute windowOutRoute windowOutPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    streamUnary, readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute,
    sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowReadRoute
  have windowOutUnary : UnaryHistory windowOut :=
    unary_cont_closed windowReadUnary provenanceUnary windowOutRoute
  exact
    ⟨streamUnary, readbackUnary, windowReadUnary, windowOutUnary, sealRowRoute,
      windowReadRoute, windowOutRoute, provenancePkg, localNamePkg, windowOutPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
