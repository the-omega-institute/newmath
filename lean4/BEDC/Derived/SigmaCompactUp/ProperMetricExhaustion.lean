import BEDC.Derived.SigmaCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.SigmaCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem SigmaCompactCarrier_proper_metric_exhaustion [AskSetup] [PackageSetup]
    {X E K B L H C P N properWindow compactWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X E properWindow →
      Cont properWindow B compactWitness →
        PkgSig bundle compactWitness pkg →
          sigmaCompactFromEventFlow
                (sigmaCompactToEventFlow (SigmaCompactUp.mk X E K B L H C P N)) =
              some (SigmaCompactUp.mk X E K B L H C P N) ∧
            Cont X E properWindow ∧ Cont properWindow B compactWitness ∧
              PkgSig bundle compactWitness pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro properWindowRoute compactWitnessRoute compactWitnessPkg
  obtain ⟨_gate, _decode, roundTrip, _emptyEncode⟩ :=
    SigmaCompactTasteGate_single_carrier_alignment
  exact
    ⟨roundTrip (SigmaCompactUp.mk X E K B L H C P N), properWindowRoute,
      compactWitnessRoute, compactWitnessPkg⟩

end BEDC.Derived.SigmaCompactUp
