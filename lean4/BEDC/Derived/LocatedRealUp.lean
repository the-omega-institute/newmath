import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealCarrierSurface [AskSetup] [PackageSetup]
    (regSeq interval schedule enclosure route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regSeq ∧ UnaryHistory interval ∧ UnaryHistory schedule ∧
    UnaryHistory enclosure ∧ Cont regSeq schedule enclosure ∧
      Cont interval enclosure route ∧ Cont route provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem LocatedRealCarrierSurface_dyadic_interval_obligation [AskSetup] [PackageSetup]
    {regSeq interval schedule enclosure route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regSeq interval schedule enclosure route provenance endpoint
        bundle pkg ->
      UnaryHistory interval ∧ UnaryHistory schedule ∧ UnaryHistory enclosure ∧
        Cont regSeq schedule enclosure ∧ Cont interval enclosure route ∧
          hsame enclosure (append regSeq schedule) ∧ hsame route (append interval enclosure) ∧
            PkgSig bundle endpoint pkg := by
  intro surface
  have intervalUnary : UnaryHistory interval :=
    surface.right.left
  have scheduleUnary : UnaryHistory schedule :=
    surface.right.right.left
  have enclosureUnary : UnaryHistory enclosure :=
    surface.right.right.right.left
  have enclosureRow : Cont regSeq schedule enclosure :=
    surface.right.right.right.right.left
  have routeRow : Cont interval enclosure route :=
    surface.right.right.right.right.right.left
  have enclosureSame : hsame enclosure (append regSeq schedule) :=
    enclosureRow
  have routeSame : hsame route (append interval enclosure) :=
    routeRow
  have pkgSig : PkgSig bundle endpoint pkg :=
    surface.right.right.right.right.right.right.right
  exact And.intro intervalUnary
    (And.intro scheduleUnary
      (And.intro enclosureUnary
        (And.intro enclosureRow
          (And.intro routeRow
            (And.intro enclosureSame
              (And.intro routeSame pkgSig))))))

end BEDC.Derived.LocatedRealUp
