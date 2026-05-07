import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.Derived.RootSystemUp

def WeylGroupWordLedger
    (support : ProbeBundle BHist) (Vector Nonzero : BHist -> Prop)
    (root : BHist) : List BHist -> Prop
  | [] => RootSystemFiniteSupportCarrier support Vector Nonzero root
  | step :: tail =>
      RootSystemFiniteSupportCarrier support Vector Nonzero step ∧
        BEDC.Derived.GroupUp.GroupSingletonCarrier step ∧
          WeylGroupWordLedger support Vector Nonzero root tail

theorem WeylGroupWordLedger_append_closure
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop} {root : BHist}
    {left right : List BHist} :
    WeylGroupWordLedger support Vector Nonzero root left ->
      WeylGroupWordLedger support Vector Nonzero root right ->
        WeylGroupWordLedger support Vector Nonzero root (left ++ right) := by
  induction left with
  | nil =>
      intro _leftLedger rightLedger
      exact rightLedger
  | cons step tail ih =>
      intro leftLedger rightLedger
      exact And.intro leftLedger.left
        (And.intro leftLedger.right.left (ih leftLedger.right.right rightLedger))

end BEDC.Derived.WeylGroupUp
