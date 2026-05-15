import BEDC.Derived.RegularCauchyTailFiberUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailFiberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailFiber_shared_fiber_route_changes_packet
    (R0 R1 W0 W1 D0 D1 T T' A H C P N : BHist)
    (_route : Cont T A C) (_route' : Cont T' A C) (hT : T ≠ T') :
    RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N ≠
      RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T' A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hpacket
  injection hpacket with _ _ _ _ _ _ hShared _ _ _ _ _
  exact hT hShared

theorem RegularCauchyTailFiberWindowProjection_changes_packet
    (R0 R1 W0 W0' W1 D0 D1 T A H C P N : BHist) (hW0 : W0 ≠ W0') :
    RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N ≠
      RegularCauchyTailFiberUp.mk R0 R1 W0' W1 D0 D1 T A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hpacket
  injection hpacket with _ _ hWindow _ _ _ _ _ _ _ _ _
  exact hW0 hWindow

theorem RegularCauchyTailFiberPacket_source_nonescape [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 d0 d1 t a h c p n sourceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFiberPacket r0 r1 w0 w1 d0 d1 t a h c p n bundle pkg →
      Cont r0 w0 sourceRead →
        Cont t a sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory sourceRead ∧ UnaryHistory sealRead ∧ Cont r0 w0 sourceRead ∧
              Cont d0 d1 t ∧ Cont t a sealRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceRoute sealRoute sealPkg
  obtain ⟨r0Unary, _r1Unary, w0Unary, _w1Unary, _d0Unary, _d1Unary, tUnary, aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _sourcePacketRoute, _classifierRoute,
    tailRoute, _sealPacketRoute, packetPkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed r0Unary w0Unary sourceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary aUnary sealRoute
  exact
    ⟨sourceUnary, sealUnary, sourceRoute, tailRoute, sealRoute, packetPkg, sealPkg⟩

end BEDC.Derived.RegularCauchyTailFiberUp
