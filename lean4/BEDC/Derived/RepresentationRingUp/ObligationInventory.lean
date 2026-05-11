import BEDC.Derived.RepresentationRingUp

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def RepresentationRingObligationRowInventory [AskSetup] [PackageSetup]
    (group ring reps directSum tensor provenance classifier ledger endpoint consumer : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
      classifier ledger endpoint bundle pkg ∧
    Cont endpoint consumer ledger ∧ PkgSig bundle endpoint pkg

theorem RepresentationRingObligationRowInventory_soundness [AskSetup] [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingObligationRowInventory group ring reps directSum tensor provenance
        classifier ledger endpoint consumer bundle pkg ->
      RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
          classifier ledger endpoint bundle pkg ∧
        hsame ledger (append provenance classifier) ∧ PkgSig bundle endpoint pkg := by
  intro inventory
  have boundary :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary inventory.left
  exact And.intro inventory.left
    (And.intro boundary.right.right.right.right.right.right.right.right.right.left
      inventory.right.right)

end BEDC.Derived.RepresentationRingUp
