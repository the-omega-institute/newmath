import BEDC.Derived.CoverageRankAlgebraUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CoverageRankAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoverageRankAlgebraCarrier [AskSetup] [PackageSetup]
    (B R T L F Q H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory L ∧ UnaryHistory F ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

def CoverageRankAlgebraClassifierStableIdentification
    (B R T L F Q H C P N B' R' T' L' F' Q' H' C' P' N' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame B B' ∧ hsame R R' ∧ hsame T T' ∧ hsame L L' ∧ hsame F F' ∧ hsame Q Q' ∧
    hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N'

theorem CoverageRankAlgebraBoundaryTriggerSeparation [AskSetup] [PackageSetup]
    {B R T L F Q H C P N B' R' T' L' F' Q' H' C' P' N' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoverageRankAlgebraCarrier B R T L F Q H C P N bundle pkg →
      CoverageRankAlgebraCarrier B' R' T' L' F' Q' H' C' P' N' bundle pkg →
        hsame R R' →
          ¬ hsame T T' →
            ¬ CoverageRankAlgebraClassifierStableIdentification
              B R T L F Q H C P N B' R' T' L' F' Q' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory
  intro _carrier _carrier' _sameRank triggerSeparated stable
  exact triggerSeparated stable.right.right.left

end BEDC.Derived.CoverageRankAlgebraUp
