import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NetClusterPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NetClusterPointUp : Type where
  | mk
      (moore directed subnet convergence compact transport replay provenance
        localName : BHist) : NetClusterPointUp
  deriving DecidableEq

def netClusterPointEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: netClusterPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: netClusterPointEncodeBHist h

def netClusterPointDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (netClusterPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (netClusterPointDecodeBHist tail)

private theorem NetClusterPointTasteGate_single_carrier_alignment_decode :
    forall h : BHist, netClusterPointDecodeBHist (netClusterPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def netClusterPointFields : NetClusterPointUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NetClusterPointUp.mk moore directed subnet convergence compact transport replay
      provenance localName =>
      [moore, directed, subnet, convergence, compact, transport, replay, provenance,
        localName]

def netClusterPointToEventFlow : NetClusterPointUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (netClusterPointFields x).map netClusterPointEncodeBHist

private def netClusterPointEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => netClusterPointEventAtDefault index rest

def netClusterPointFromEventFlow (ef : EventFlow) : Option NetClusterPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NetClusterPointUp.mk
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 0 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 1 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 2 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 3 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 4 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 5 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 6 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 7 ef))
      (netClusterPointDecodeBHist (netClusterPointEventAtDefault 8 ef)))

private theorem NetClusterPointTasteGate_single_carrier_alignment_round_trip
    (x : NetClusterPointUp) :
    netClusterPointFromEventFlow (netClusterPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk moore directed subnet convergence compact transport replay provenance localName =>
      change
        some
          (NetClusterPointUp.mk
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist moore))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist directed))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist subnet))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist convergence))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist compact))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist transport))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist replay))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist provenance))
            (netClusterPointDecodeBHist (netClusterPointEncodeBHist localName))) =
          some
            (NetClusterPointUp.mk moore directed subnet convergence compact transport
              replay provenance localName)
      rw [NetClusterPointTasteGate_single_carrier_alignment_decode moore,
        NetClusterPointTasteGate_single_carrier_alignment_decode directed,
        NetClusterPointTasteGate_single_carrier_alignment_decode subnet,
        NetClusterPointTasteGate_single_carrier_alignment_decode convergence,
        NetClusterPointTasteGate_single_carrier_alignment_decode compact,
        NetClusterPointTasteGate_single_carrier_alignment_decode transport,
        NetClusterPointTasteGate_single_carrier_alignment_decode replay,
        NetClusterPointTasteGate_single_carrier_alignment_decode provenance,
        NetClusterPointTasteGate_single_carrier_alignment_decode localName]

private theorem NetClusterPointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NetClusterPointUp} :
    netClusterPointToEventFlow x = netClusterPointToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      netClusterPointFromEventFlow (netClusterPointToEventFlow x) =
        netClusterPointFromEventFlow (netClusterPointToEventFlow y) :=
    congrArg netClusterPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NetClusterPointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NetClusterPointTasteGate_single_carrier_alignment_round_trip y)))

instance netClusterPointBHistCarrier : BHistCarrier NetClusterPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := netClusterPointToEventFlow
  fromEventFlow := netClusterPointFromEventFlow

instance netClusterPointChapterTasteGate : ChapterTasteGate NetClusterPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change netClusterPointFromEventFlow (netClusterPointToEventFlow x) = some x
    exact NetClusterPointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NetClusterPointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate NetClusterPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  netClusterPointChapterTasteGate

theorem NetClusterPointTasteGate_single_carrier_alignment (x : NetClusterPointUp) :
    (exists moore directed subnet convergence compact transport replay provenance
        localName : BHist,
      x =
        NetClusterPointUp.mk moore directed subnet convergence compact transport replay
          provenance localName) ∧
      Nonempty (BHistCarrier NetClusterPointUp) ∧
        Nonempty (ChapterTasteGate NetClusterPointUp) ∧
          netClusterPointEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk moore directed subnet convergence compact transport replay provenance localName =>
      exact
        ⟨⟨moore, directed, subnet, convergence, compact, transport, replay, provenance,
            localName, rfl⟩,
          ⟨netClusterPointBHistCarrier⟩,
          ⟨netClusterPointChapterTasteGate⟩,
          rfl⟩

end BEDC.Derived.NetClusterPointUp
