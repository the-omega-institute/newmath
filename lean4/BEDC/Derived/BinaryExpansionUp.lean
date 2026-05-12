import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinaryExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BinaryExpansionPacket [AskSetup] [PackageSetup]
    (digits windows approximation regular realSeal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
    UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
          Cont transport route provenance ∧ PkgSig bundle provenance pkg

theorem BinaryExpansionPacket_prefix_window_stability [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert digits'
      windows' approximation' regular' realSeal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg ->
      hsame windows windows' -> hsame digits digits' -> hsame regular regular' ->
        Cont windows' digits' approximation' -> Cont approximation' regular' realSeal' ->
          BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport
              route provenance nameCert bundle pkg ∧
            hsame approximation approximation' ∧ hsame realSeal realSeal' := by
  intro packet sameWindows sameDigits sameRegular approximationRow' realSealRow'
  have approximationRow : Cont windows digits approximation :=
    packet.right.right.right.right.right.right.right.right.right.left
  have realSealRow : Cont approximation regular realSeal :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have sameApproximation : hsame approximation approximation' :=
    cont_respects_hsame sameWindows sameDigits approximationRow approximationRow'
  have sameRealSeal : hsame realSeal realSeal' :=
    cont_respects_hsame sameApproximation sameRegular realSealRow realSealRow'
  have transported :
      BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport route
        provenance nameCert bundle pkg :=
    ⟨unary_transport packet.left sameDigits,
      unary_transport packet.right.left sameWindows,
      unary_transport packet.right.right.left sameApproximation,
      unary_transport packet.right.right.right.left sameRegular,
      unary_transport packet.right.right.right.right.left sameRealSeal,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      approximationRow',
      realSealRow',
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right⟩
  exact ⟨transported, sameApproximation, sameRealSeal⟩

end BEDC.Derived.BinaryExpansionUp
