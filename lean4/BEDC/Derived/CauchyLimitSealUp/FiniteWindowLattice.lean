import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyLimitSealCarrier_middle_window_meet_determinacy [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint windowA
      observationA realReadA consumerA windowB observationB realReadB consumerB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source windowA ->
        Cont windowA dyadic observationA ->
          Cont observationA diagonal realReadA ->
            Cont realReadA endpoint consumerA ->
              Cont schedule source windowB ->
                Cont windowB dyadic observationB ->
                  Cont observationB diagonal realReadB ->
                    Cont realReadB endpoint consumerB ->
                      hsame dyadic observationA ->
                        hsame dyadic observationB ->
                          hsame realReadA realReadB ∧ hsame sealRow realReadA ∧
                            hsame sealRow realReadB ∧
                              hsame endpoint (append provenance localCert) ∧
                                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindowA windowDyadicObservationA observationDiagonalReadA
    readEndpointConsumerA scheduleSourceWindowB windowDyadicObservationB
    observationDiagonalReadB readEndpointConsumerB sameDyadicObservationA
    sameDyadicObservationB
  have pulledA :=
    CauchyLimitSealCarrier_scheduled_window_pullback carrier scheduleSourceWindowA
      windowDyadicObservationA observationDiagonalReadA readEndpointConsumerA
      sameDyadicObservationA
  have pulledB :=
    CauchyLimitSealCarrier_scheduled_window_pullback carrier scheduleSourceWindowB
      windowDyadicObservationB observationDiagonalReadB readEndpointConsumerB
      sameDyadicObservationB
  obtain ⟨_windowAUnary, _observationAUnary, _realReadAUnary, _consumerAUnary,
    sameSealReadA, sameEndpoint, endpointPkg⟩ := pulledA
  obtain ⟨_windowBUnary, _observationBUnary, _realReadBUnary, _consumerBUnary,
    sameSealReadB, _sameEndpointB, _endpointPkgB⟩ := pulledB
  have sameReads : hsame realReadA realReadB :=
    hsame_trans (hsame_symm sameSealReadA) sameSealReadB
  exact ⟨sameReads, sameSealReadA, sameSealReadB, sameEndpoint, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
