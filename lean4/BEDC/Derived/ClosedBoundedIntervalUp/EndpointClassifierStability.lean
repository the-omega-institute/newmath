import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_endpoint_classifier_stability [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported endpointRead containmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont lower upper endpointRead →
        Cont endpointRead rational containmentRead →
          PkgSig bundle containmentRead pkg →
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory endpointRead ∧ UnaryHistory containmentRead ∧
                Cont lower upper order ∧ Cont lower upper endpointRead ∧
                  Cont endpointRead rational containmentRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle containmentRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet endpointRoute containmentRoute containmentPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, _dyadicUnary, _streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, packetEndpointRoute, _packetContainmentRoute,
    _packetSealRoute, _packetReplayRoute, _packetNameRoute, provenancePkg, _localNamePkg⟩ :=
      packet
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lowerUnary upperUnary endpointRoute
  have containmentUnary : UnaryHistory containmentRead :=
    unary_cont_closed endpointUnary rationalUnary containmentRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, endpointUnary, containmentUnary, packetEndpointRoute,
      endpointRoute, containmentRoute, provenancePkg, containmentPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
