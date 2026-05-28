import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_located_endpoint_readback [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported endpointRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont order stream endpointRead ->
        Cont endpointRead readback regularRead ->
          Cont regularRead sealRow realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
                UnaryHistory endpointRead ∧ UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                  Cont lower upper order ∧ Cont order stream endpointRead ∧
                    Cont endpointRead readback regularRead ∧ Cont regularRead sealRow realRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet endpointRoute regularRoute realRoute realPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, _dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, carrierEndpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed orderUnary streamUnary endpointRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary readbackUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary sealRowUnary realRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, endpointUnary, regularUnary, realUnary,
      carrierEndpointRoute, endpointRoute, regularRoute, realRoute, provenancePkg, realPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
