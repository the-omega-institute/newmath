import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyTriangleBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTriangleBoundCarrier [AskSetup] [PackageSetup]
    (dm dn im inn tolerance endpointLegs middleLeg transport route provenance nameCert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dm ∧ UnaryHistory dn ∧ UnaryHistory im ∧ UnaryHistory inn ∧
    UnaryHistory endpointLegs ∧ UnaryHistory middleLeg ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ Cont dm im transport ∧
        Cont im inn route ∧ Cont inn dn provenance ∧
          Cont endpointLegs middleLeg tolerance ∧ PkgSig bundle nameCert pkg

theorem RegularCauchyTriangleBoundCarrier_diagonal_regular_route
    [AskSetup] [PackageSetup]
    {dm dn im inn tolerance endpointLegs middleLeg transport route provenance nameCert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTriangleBoundCarrier dm dn im inn tolerance endpointLegs middleLeg
        transport route provenance nameCert bundle pkg →
      UnaryHistory dm ∧ UnaryHistory dn ∧ UnaryHistory im ∧ UnaryHistory inn ∧
        Cont dm im transport ∧ Cont im inn route ∧ Cont inn dn provenance ∧
          Cont endpointLegs middleLeg tolerance ∧ PkgSig bundle nameCert pkg := by
  intro packet
  exact
    ⟨packet.left, packet.right.left, packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.RegularCauchyTriangleBoundUp
