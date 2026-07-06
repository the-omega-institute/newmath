import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.BrzozowskiDerivativeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def BrzozowskiDerivativeCarrier
    (Sigma W L R «partial» nu C Q delta q0 F mu H K P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  hsame H H ∧ Cont K W q0 ∧ hsame Sigma Sigma ∧ hsame «partial» «partial» ∧
    hsame nu nu ∧ hsame delta delta ∧ hsame F F ∧ hsame P P ∧ hsame N N

theorem BrzozowskiDerivativeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Sigma W L R «partial» nu C Q delta q0 F mu H K P N : BHist}
    (h : BrzozowskiDerivativeCarrier Sigma W L R «partial» nu C Q delta q0 F mu H K P N) :
    BrzozowskiDerivativeCarrier Sigma W L R «partial» nu C Q delta q0 F mu H K P N ∧
      hsame H H ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame AskSetup PackageSetup
  have carrier := h
  obtain ⟨handoff, _startRoute, _alphabet, _table, _nullability, _transition, _accepting,
    provenance, localName⟩ := h
  exact ⟨carrier, handoff, provenance, localName⟩

end BEDC.Derived.BrzozowskiDerivativeUp
