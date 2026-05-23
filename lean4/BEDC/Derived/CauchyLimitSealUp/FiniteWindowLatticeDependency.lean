import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_finite_window_lattice_dependency [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint window
      observation realRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            Cont realRead endpoint consumerRead ->
              hsame dyadic observation ->
                UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                  UnaryHistory consumerRead ∧ hsame sealRow realRead ∧
                    hsame endpoint (append provenance localCert) ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    readEndpointConsumer sameDyadicObservation
  exact
    CauchyLimitSealCarrier_scheduled_window_pullback carrier scheduleSourceWindow
      windowDyadicObservation observationDiagonalRead readEndpointConsumer sameDyadicObservation

end BEDC.Derived.CauchyLimitSealUp
