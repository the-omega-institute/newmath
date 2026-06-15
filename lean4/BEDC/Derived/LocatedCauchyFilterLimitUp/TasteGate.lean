import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyFilterLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyFilterLimitUp : Type where
  | mk (B F G S R D A H C P N : BHist) : LocatedCauchyFilterLimitUp

def locatedCauchyFilterLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyFilterLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyFilterLimitEncodeBHist h

def locatedCauchyFilterLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyFilterLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyFilterLimitDecodeBHist tail)

private theorem LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyFilterLimitFields : LocatedCauchyFilterLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyFilterLimitUp.mk B F G S R D A H C P N => [B, F, G, S, R, D, A, H, C, P, N]

def locatedCauchyFilterLimitToEventFlow : LocatedCauchyFilterLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCauchyFilterLimitFields x).map locatedCauchyFilterLimitEncodeBHist

private def locatedCauchyFilterLimitRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCauchyFilterLimitRawAt index rest

def locatedCauchyFilterLimitFromEventFlow
    (flow : EventFlow) : Option LocatedCauchyFilterLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyFilterLimitUp.mk
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 0 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 1 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 2 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 3 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 4 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 5 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 6 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 7 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 8 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 9 flow))
      (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitRawAt 10 flow)))

private theorem LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCauchyFilterLimitUp,
      locatedCauchyFilterLimitFromEventFlow
          (locatedCauchyFilterLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F G S R D A H C P N =>
      change
        some
          (LocatedCauchyFilterLimitUp.mk
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist B))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist F))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist G))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist S))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist R))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist D))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist A))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist H))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist C))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist P))
            (locatedCauchyFilterLimitDecodeBHist (locatedCauchyFilterLimitEncodeBHist N))) =
          some (LocatedCauchyFilterLimitUp.mk B F G S R D A H C P N)
      rw [LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode B,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode F,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode G,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode S,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode R,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode D,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode A,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode H,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode C,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode P,
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCauchyFilterLimitUp} :
    locatedCauchyFilterLimitToEventFlow x =
        locatedCauchyFilterLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyFilterLimitFromEventFlow (locatedCauchyFilterLimitToEventFlow x) =
        locatedCauchyFilterLimitFromEventFlow (locatedCauchyFilterLimitToEventFlow y) :=
    congrArg locatedCauchyFilterLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCauchyFilterLimitBHistCarrier :
    BHistCarrier LocatedCauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyFilterLimitToEventFlow
  fromEventFlow := locatedCauchyFilterLimitFromEventFlow

instance locatedCauchyFilterLimitChapterTasteGate :
    ChapterTasteGate LocatedCauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyFilterLimitFromEventFlow
          (locatedCauchyFilterLimitToEventFlow x) =
        some x
    exact LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedCauchyFilterLimitTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedCauchyFilterLimitUp) ∧
      Nonempty (ChapterTasteGate LocatedCauchyFilterLimitUp) ∧
        ∀ x y : LocatedCauchyFilterLimitUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨locatedCauchyFilterLimitBHistCarrier⟩,
      ⟨locatedCauchyFilterLimitChapterTasteGate⟩,
      fun _ _ heq =>
        LocatedCauchyFilterLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq⟩

end BEDC.Derived.LocatedCauchyFilterLimitUp
