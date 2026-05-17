import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_componentwise_transport [AskSetup] [PackageSetup]
    {Q B S K H C P N Qp Bp Sp Kp Hp Cp Pp Np : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyWitnessLedgerUp.mk Q B S K H C P N =
        CauchyWitnessLedgerUp.mk Qp Bp Sp Kp Hp Cp Pp Np →
      PkgSig bundle N pkg →
        hsame Q Qp ∧ hsame B Bp ∧ hsame S Sp ∧ hsame K Kp ∧ hsame H Hp ∧
          hsame C Cp ∧ hsame P Pp ∧ hsame N Np ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame
  intro samePacket namePkg
  cases samePacket
  exact
    ⟨hsame_refl Q, hsame_refl B, hsame_refl S, hsame_refl K, hsame_refl H,
      hsame_refl C, hsame_refl P, hsame_refl N, namePkg⟩

end BEDC.Derived.CauchyWitnessLedgerUp
