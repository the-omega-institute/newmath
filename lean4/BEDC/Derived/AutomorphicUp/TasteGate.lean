import BEDC.Derived.AutomorphicUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AutomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AutomorphicUp : Type where
  | mk (carrier core domain value : BHist) : AutomorphicUp
  deriving DecidableEq

def automorphicEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: automorphicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: automorphicEncodeBHist h

def automorphicDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (automorphicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (automorphicDecodeBHist tail)

private theorem AutomorphicTasteGate_single_carrier_alignment_decode :
    forall h : BHist, automorphicDecodeBHist (automorphicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def automorphicFields : AutomorphicUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AutomorphicUp.mk carrier core domain value => [carrier, core, domain, value]

def automorphicToEventFlow : AutomorphicUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (automorphicFields x).map automorphicEncodeBHist

private def automorphicEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => automorphicEventAtDefault index rest

def automorphicFromEventFlow : EventFlow -> Option AutomorphicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AutomorphicUp.mk
        (automorphicDecodeBHist (automorphicEventAtDefault 0 ef))
        (automorphicDecodeBHist (automorphicEventAtDefault 1 ef))
        (automorphicDecodeBHist (automorphicEventAtDefault 2 ef))
        (automorphicDecodeBHist (automorphicEventAtDefault 3 ef)))

private theorem AutomorphicTasteGate_single_carrier_alignment_round_trip :
    forall x : AutomorphicUp,
      automorphicFromEventFlow (automorphicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk carrier core domain value =>
      change
        some
          (AutomorphicUp.mk
            (automorphicDecodeBHist (automorphicEncodeBHist carrier))
            (automorphicDecodeBHist (automorphicEncodeBHist core))
            (automorphicDecodeBHist (automorphicEncodeBHist domain))
            (automorphicDecodeBHist (automorphicEncodeBHist value))) =
          some (AutomorphicUp.mk carrier core domain value)
      rw [AutomorphicTasteGate_single_carrier_alignment_decode carrier,
        AutomorphicTasteGate_single_carrier_alignment_decode core,
        AutomorphicTasteGate_single_carrier_alignment_decode domain,
        AutomorphicTasteGate_single_carrier_alignment_decode value]

private theorem AutomorphicTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AutomorphicUp} :
    automorphicToEventFlow x = automorphicToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      automorphicFromEventFlow (automorphicToEventFlow x) =
        automorphicFromEventFlow (automorphicToEventFlow y) :=
    congrArg automorphicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AutomorphicTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AutomorphicTasteGate_single_carrier_alignment_round_trip y)))

instance automorphicBHistCarrier : BHistCarrier AutomorphicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := automorphicToEventFlow
  fromEventFlow := automorphicFromEventFlow

instance automorphicChapterTasteGate : ChapterTasteGate AutomorphicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change automorphicFromEventFlow (automorphicToEventFlow x) = some x
    exact AutomorphicTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AutomorphicTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AutomorphicTasteGate_single_carrier_alignment :
    (forall x : AutomorphicUp, exists h : BHist, List.Mem h (automorphicFields x)) /\
      Nonempty (BHistCarrier AutomorphicUp) /\
        Nonempty (ChapterTasteGate AutomorphicUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨by
      intro x
      cases x with
      | mk carrier _core _domain _value =>
          exact ⟨carrier, List.Mem.head _⟩,
      ⟨automorphicBHistCarrier⟩,
      ⟨automorphicChapterTasteGate⟩⟩

end BEDC.Derived.AutomorphicUp
