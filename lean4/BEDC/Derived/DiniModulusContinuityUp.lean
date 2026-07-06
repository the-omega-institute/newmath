import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.DiniModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def DiniModulusContinuityCarrier (W R D T E H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  hsame H H ∧ Cont C W E ∧ hsame R R ∧ hsame D D ∧ hsame T T ∧ hsame P P ∧
    hsame N N

theorem DiniModulusContinuityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {W R D T E H C P N : BHist}
    (h : DiniModulusContinuityCarrier W R D T E H C P N) :
    DiniModulusContinuityCarrier W R D T E H C P N ∧ hsame H H ∧ hsame P P ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame AskSetup PackageSetup
  have carrier := h
  obtain ⟨handoff, _readback, _dini, _dyadic, _tolerance, provenance, localName⟩ := h
  exact ⟨carrier, handoff, provenance, localName⟩

end BEDC.Derived.DiniModulusContinuityUp
