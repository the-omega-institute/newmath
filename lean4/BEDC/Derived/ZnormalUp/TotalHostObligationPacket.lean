import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def ZnormalTotalHostObligationPacket [AskSetup] [PackageSetup]
    (typed fuel terminal normal continuation transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
      bundle pkg ∧
    Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
      Cont continuation transports routes ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg

theorem ZnormalTotalHostObligationPacket_rows [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalTotalHostObligationPacket typed fuel terminal normal continuation transports routes
        provenance name bundle pkg →
      ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
          bundle pkg ∧
        Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
          Cont continuation transports routes ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro packet
  exact packet

end BEDC.Derived.ZnormalUp
