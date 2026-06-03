import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_net_unblock_package [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported densityRead netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont dyadic stream densityRead →
        Cont densityRead readback netRead →
          PkgSig bundle netRead pkg →
            UnaryHistory densityRead ∧ UnaryHistory netRead ∧ Cont lower upper order ∧
              Cont order rational dyadic ∧ Cont dyadic stream densityRead ∧
                Cont densityRead readback netRead ∧ Cont stream readback sealRow ∧
                  Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle netRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet densityRoute netRoute netPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, endpointRoute, containmentRoute,
    sealRoute, transportRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed dyadicUnary streamUnary densityRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed densityUnary readbackUnary netRoute
  exact
    ⟨densityUnary, netUnary, endpointRoute, containmentRoute, densityRoute, netRoute, sealRoute,
      transportRoute, provenancePkg, netPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
