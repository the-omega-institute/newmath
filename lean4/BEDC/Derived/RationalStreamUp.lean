import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalStreamPacket [AskSetup] [PackageSetup]
    (index schedule pointRows classifierRows transport window provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory pointRows ∧
    UnaryHistory classifierRows ∧ UnaryHistory transport ∧ UnaryHistory window ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont index schedule window ∧
        Cont pointRows classifierRows transport ∧ Cont transport window provenance ∧
          PkgSig bundle provenance pkg

theorem RationalStreamPacket_regseqrat_finite_window_surface [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transport window provenance nameRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transport window provenance
        nameRow bundle pkg ->
      Cont window nameRow consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory pointRows ∧
            UnaryHistory classifierRows ∧ UnaryHistory window ∧ UnaryHistory consumer ∧
              Cont index schedule window ∧ Cont window nameRow consumer ∧
                PkgSig bundle consumer pkg := by
  intro packet consumerRow consumerPkg
  obtain ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, _transportUnary,
    windowUnary, _provenanceUnary, nameRowUnary, indexScheduleRow, _pointClassifierRow,
    _transportWindowRow, _provenancePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary nameRowUnary consumerRow
  exact
    ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, windowUnary,
      consumerUnary, indexScheduleRow, consumerRow, consumerPkg⟩

end BEDC.Derived.RationalStreamUp
