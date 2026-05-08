import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.GroundCompiler.SourceChannel

open BEDC.GroundCompiler.EventFlow

def SourceLevelRelation : Type :=
  RawEvent -> RawEvent -> Prop

def SourceCarryLedger (w v : RawEvent) : EventFlow :=
  [w, v]

theorem ledger_records_distinguish_ordered_pairs
    {w v w' v' : RawEvent} :
    SourceCarryLedger w v = SourceCarryLedger w' v' -> w = w' /\ v = v' := by
  intro h
  cases h
  constructor
  · rfl
  · rfl

end BEDC.GroundCompiler.SourceChannel
