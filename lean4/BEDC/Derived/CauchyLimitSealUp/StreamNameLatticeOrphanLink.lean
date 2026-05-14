import BEDC.Derived.CauchyLimitSealUp.StreamNameDependency

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_streamname_lattice_orphan_link [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead consumerRead regularRead latticeMeet latticeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            Cont realRead endpoint consumerRead ->
              Cont window source regularRead ->
                Cont regularRead window latticeMeet ->
                  Cont latticeMeet dyadic latticeRead ->
                    hsame dyadic observation ->
                      UnaryHistory window ∧ UnaryHistory regularRead ∧
                        UnaryHistory latticeMeet ∧ UnaryHistory latticeRead ∧
                          UnaryHistory realRead ∧ UnaryHistory consumerRead ∧
                            Cont regularRead window latticeMeet ∧
                              Cont latticeMeet dyadic latticeRead ∧
                                hsame sealRow realRead ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    readEndpointConsumer windowSourceRegular regularWindowLattice latticeDyadicRead
    sameDyadicObservation
  have dependency :=
    CauchyLimitSealCarrier_streamname_dependency carrier scheduleSourceWindow
      windowDyadicObservation observationDiagonalRead readEndpointConsumer
      windowSourceRegular sameDyadicObservation
  obtain ⟨windowUnary, _observationUnary, realReadUnary, consumerReadUnary,
    regularReadUnary, _scheduleSourceWindow, _windowDyadicObservation,
    _observationDiagonalRead, _readEndpointConsumer, _windowSourceRegular,
    sealSameRead, endpointPkg⟩ := dependency
  have latticeMeetUnary : UnaryHistory latticeMeet :=
    unary_cont_closed regularReadUnary windowUnary regularWindowLattice
  obtain ⟨_sourceUnary, _scheduleUnary, dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, _endpointPkgCarrier⟩ := carrier
  have latticeReadUnary : UnaryHistory latticeRead :=
    unary_cont_closed latticeMeetUnary dyadicUnary latticeDyadicRead
  exact
    ⟨windowUnary, regularReadUnary, latticeMeetUnary, latticeReadUnary, realReadUnary,
      consumerReadUnary, regularWindowLattice, latticeDyadicRead, sealSameRead,
      endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
