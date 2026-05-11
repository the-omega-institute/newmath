import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegSeqRatStreamCarrier [AskSetup] [PackageSetup]
    (schedule index endpoint radius regularity transport _provenance «seal» : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory index ∧ UnaryHistory endpoint ∧
    UnaryHistory radius ∧ UnaryHistory transport ∧ Cont schedule index endpoint ∧
      Cont endpoint radius regularity ∧ Cont regularity transport «seal» ∧
        PkgSig bundle «seal» pkg

theorem RegSeqRatStreamCarrier_obligation_surface [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity transport _provenance «seal» : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity transport provenance «seal»
        bundle pkg ->
      UnaryHistory schedule ∧ UnaryHistory index ∧ UnaryHistory endpoint ∧
        UnaryHistory radius ∧ UnaryHistory regularity ∧ UnaryHistory transport ∧
          UnaryHistory «seal» ∧ Cont schedule index endpoint ∧ Cont endpoint radius regularity ∧
            Cont regularity transport «seal» ∧ PkgSig bundle «seal» pkg := by
  intro carrier
  have scheduleUnary : UnaryHistory schedule :=
    carrier.left
  have indexUnary : UnaryHistory index :=
    carrier.right.left
  have endpointUnary : UnaryHistory endpoint :=
    carrier.right.right.left
  have radiusUnary : UnaryHistory radius :=
    carrier.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    carrier.right.right.right.right.left
  have scheduleRow : Cont schedule index endpoint :=
    carrier.right.right.right.right.right.left
  have regularityRow : Cont endpoint radius regularity :=
    carrier.right.right.right.right.right.right.left
  have sealRow : Cont regularity transport «seal» :=
    carrier.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle «seal» pkg :=
    carrier.right.right.right.right.right.right.right.right
  have regularityUnary : UnaryHistory regularity :=
    unary_cont_closed endpointUnary radiusUnary regularityRow
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed regularityUnary transportUnary sealRow
  exact
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary, transportUnary,
      sealUnary, scheduleRow, regularityRow, sealRow, pkgSig⟩

end BEDC.Derived.RegSeqRatUp
