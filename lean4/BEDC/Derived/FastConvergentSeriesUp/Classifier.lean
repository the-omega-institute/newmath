import BEDC.Derived.FastConvergentSeriesUp

namespace BEDC.Derived.FastConvergentSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def FastConvergentSeriesClassifierSpec [AskSetup] [PackageSetup]
    (series seq partialSums schedule tailLedger regReadback realSeal transports routes
      provenance nameCert series' seq' partialSums' schedule' tailLedger' regReadback'
      realSeal' transports' routes' provenance' nameCert' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback realSeal
      transports routes provenance nameCert bundle pkg ∧
    FastConvergentSeriesCarrier series' seq' partialSums' schedule' tailLedger' regReadback'
      realSeal' transports' routes' provenance' nameCert' bundle pkg ∧
      hsame partialSums partialSums' ∧ hsame tailLedger tailLedger' ∧
        hsame regReadback regReadback' ∧ hsame realSeal realSeal' ∧
          hsame provenance provenance'

theorem FastConvergentSeriesClassifierSpec_refl [AskSetup] [PackageSetup]
    {series seq partialSums schedule tailLedger regReadback realSeal transports routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastConvergentSeriesCarrier series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert bundle pkg ->
      FastConvergentSeriesClassifierSpec series seq partialSums schedule tailLedger regReadback
        realSeal transports routes provenance nameCert series seq partialSums schedule tailLedger
        regReadback realSeal transports routes provenance nameCert bundle pkg := by
  intro carrier
  exact ⟨carrier, carrier, hsame_refl partialSums, hsame_refl tailLedger,
    hsame_refl regReadback, hsame_refl realSeal, hsame_refl provenance⟩

end BEDC.Derived.FastConvergentSeriesUp
