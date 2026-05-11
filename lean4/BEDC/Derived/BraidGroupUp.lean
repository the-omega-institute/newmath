import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BraidGroupUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BraidGroupArtinPacket [AskSetup] [PackageSetup]
    (strand word moveLedger classifier dependency endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  PositiveUnaryDenominator strand ∧ UnaryHistory word ∧ UnaryHistory moveLedger ∧
    UnaryHistory dependency ∧ Cont strand word moveLedger ∧
      Cont moveLedger dependency classifier ∧ Cont classifier word endpoint ∧
        PkgSig bundle endpoint pkg

theorem BraidGroupArtinPacket_knot_closure_empty_boundary [AskSetup] [PackageSetup]
    {strand word moveLedger classifier dependency endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word moveLedger classifier dependency endpoint bundle pkg ->
      hsame endpoint BHist.Empty ->
        hsame classifier BHist.Empty ∧ hsame word BHist.Empty := by
  intro packet endpointEmpty
  have endpointRow : Cont classifier word endpoint :=
    packet.right.right.right.right.right.right.left
  have appendedEmpty : append classifier word = BHist.Empty := by
    cases endpointRow
    exact endpointEmpty
  have parts : classifier = BHist.Empty ∧ word = BHist.Empty :=
    append_eq_empty_iff.mp appendedEmpty
  exact And.intro parts.left parts.right

end BEDC.Derived.BraidGroupUp
