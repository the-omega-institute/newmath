import BEDC.Derived.SubjectFreeObservationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectFreeObservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectFreeObservationCarrier [AskSetup] [PackageSetup]
    (O H K D L C P N observationRead ledgerRead eventRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory D ∧
    UnaryHistory L ∧ Cont O H observationRead ∧ Cont K D ledgerRead ∧
      Cont L C eventRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

end BEDC.Derived.SubjectFreeObservationUp
