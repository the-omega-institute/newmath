import BEDC.Derived.CauchyModulusMeetUp

namespace BEDC.Derived.CauchyModulusMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusMeetUp_StdBridge [AskSetup] [PackageSetup]
    {s0 s1 mu0 mu1 mu h c p n bridgeRead bridgeOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusMeetPacket s0 s1 mu0 mu1 mu h c p n bundle pkg ->
      Cont mu n bridgeRead ->
        Cont bridgeRead p bridgeOut ->
          PkgSig bundle bridgeOut pkg ->
            UnaryHistory bridgeRead ∧ UnaryHistory bridgeOut ∧ hsame p n ∧
              Cont h c mu ∧ Cont mu n bridgeRead ∧ Cont bridgeRead p bridgeOut ∧
                PkgSig bundle p pkg ∧ PkgSig bundle bridgeOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet bridgeReadRow bridgeOutRow bridgePkg
  obtain ⟨_s0Unary, _s1Unary, _mu0Unary, _mu1Unary, muUnary, _hUnary, _cUnary,
    pUnary, nUnary, _s0Mu0H, _s1Mu1C, hCMu, samePN, pPkg⟩ := packet
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed muUnary nUnary bridgeReadRow
  have bridgeOutUnary : UnaryHistory bridgeOut :=
    unary_cont_closed bridgeReadUnary pUnary bridgeOutRow
  exact
    ⟨bridgeReadUnary, bridgeOutUnary, samePN, hCMu, bridgeReadRow, bridgeOutRow, pPkg,
      bridgePkg⟩

end BEDC.Derived.CauchyModulusMeetUp
