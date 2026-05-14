import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailFusionCarrier [AskSetup] [PackageSetup]
    (Q X W D T M R L H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory Q ∧ UnaryHistory X ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory T ∧ UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory L ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont Q X W ∧ Cont W D T ∧ Cont T M R ∧ Cont H C P ∧
          hsame L (append R N) ∧ PkgSig bundle N pkg

theorem RegularCauchyTailFusionCarrier_tail_meet_handoff [AskSetup] [PackageSetup]
    {Q X W D T M R L H C P N tailRead diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailFusionCarrier Q X W D T M R L H C P N bundle pkg ->
      Cont T M tailRead ->
        Cont tailRead R diagonalRead ->
          UnaryHistory tailRead ∧ UnaryHistory diagonalRead ∧ Cont T M tailRead ∧
            Cont tailRead R diagonalRead ∧ hsame L (append R N) ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier tailRoute diagonalRoute
  obtain ⟨_qUnary, _xUnary, _wUnary, _dUnary, tailUnary, meetUnary, diagonalUnary,
    _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _precisionWindow, _windowTail, _tailMeet, _transportRoute, sealSame, namePkg⟩ :=
    carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed tailUnary meetUnary tailRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed tailReadUnary diagonalUnary diagonalRoute
  exact ⟨tailReadUnary, diagonalReadUnary, tailRoute, diagonalRoute, sealSame, namePkg⟩

end BEDC.Derived.RegularCauchyTailFusionUp
