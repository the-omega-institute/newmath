import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorelSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BorelSetUp : Type where
  | mk (X O M G R H C P N : BHist) : BorelSetUp
  deriving DecidableEq

def borelSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: borelSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: borelSetEncodeBHist h

def borelSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (borelSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (borelSetDecodeBHist tail)

private theorem BorelSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, borelSetDecodeBHist (borelSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BorelSetTasteGate_single_carrier_alignment_fields : BorelSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorelSetUp.mk X O M G R H C P N => [X, O, M, G, R, H, C, P, N]

def BorelSetTasteGate_single_carrier_alignment_toEventFlow : BorelSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BorelSetTasteGate_single_carrier_alignment_fields x).map borelSetEncodeBHist

private def BorelSetTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => BorelSetTasteGate_single_carrier_alignment_eventAt index rest

def BorelSetTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BorelSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BorelSetUp.mk
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 0 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 1 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 2 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 3 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 4 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 5 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 6 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 7 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem BorelSetTasteGate_single_carrier_alignment_round_trip
    (x : BorelSetUp) :
    BorelSetTasteGate_single_carrier_alignment_fromEventFlow
        (BorelSetTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X O M G R H C P N =>
      change
        some
          (BorelSetUp.mk
            (borelSetDecodeBHist (borelSetEncodeBHist X))
            (borelSetDecodeBHist (borelSetEncodeBHist O))
            (borelSetDecodeBHist (borelSetEncodeBHist M))
            (borelSetDecodeBHist (borelSetEncodeBHist G))
            (borelSetDecodeBHist (borelSetEncodeBHist R))
            (borelSetDecodeBHist (borelSetEncodeBHist H))
            (borelSetDecodeBHist (borelSetEncodeBHist C))
            (borelSetDecodeBHist (borelSetEncodeBHist P))
            (borelSetDecodeBHist (borelSetEncodeBHist N))) =
          some (BorelSetUp.mk X O M G R H C P N)
      rw [BorelSetTasteGate_single_carrier_alignment_decode_encode X,
        BorelSetTasteGate_single_carrier_alignment_decode_encode O,
        BorelSetTasteGate_single_carrier_alignment_decode_encode M,
        BorelSetTasteGate_single_carrier_alignment_decode_encode G,
        BorelSetTasteGate_single_carrier_alignment_decode_encode R,
        BorelSetTasteGate_single_carrier_alignment_decode_encode H,
        BorelSetTasteGate_single_carrier_alignment_decode_encode C,
        BorelSetTasteGate_single_carrier_alignment_decode_encode P,
        BorelSetTasteGate_single_carrier_alignment_decode_encode N]

private theorem BorelSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BorelSetUp} :
    BorelSetTasteGate_single_carrier_alignment_toEventFlow x =
        BorelSetTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BorelSetTasteGate_single_carrier_alignment_fromEventFlow
          (BorelSetTasteGate_single_carrier_alignment_toEventFlow x) =
        BorelSetTasteGate_single_carrier_alignment_fromEventFlow
          (BorelSetTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BorelSetTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BorelSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BorelSetTasteGate_single_carrier_alignment_round_trip y)))

instance BorelSetTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BorelSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BorelSetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BorelSetTasteGate_single_carrier_alignment_fromEventFlow

instance BorelSetTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BorelSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BorelSetTasteGate_single_carrier_alignment_fromEventFlow
          (BorelSetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BorelSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BorelSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BorelSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, borelSetDecodeBHist (borelSetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BorelSetUp) ∧
        Nonempty (ChapterTasteGate BorelSetUp) ∧
          borelSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BorelSetTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨BorelSetTasteGate_single_carrier_alignment_BHistCarrier⟩,
        ⟨⟨BorelSetTasteGate_single_carrier_alignment_ChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.BorelSetUp
