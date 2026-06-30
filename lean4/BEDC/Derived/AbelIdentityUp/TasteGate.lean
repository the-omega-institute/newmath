import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelIdentityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelIdentityUp : Type where
  | mk (Q D W I S R E H C P N : BHist) : AbelIdentityUp
  deriving DecidableEq

def abelIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelIdentityEncodeBHist h

def abelIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelIdentityDecodeBHist tail)

private theorem AbelIdentityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, abelIdentityDecodeBHist (abelIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelIdentityToEventFlow : AbelIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AbelIdentityUp.mk Q D W I S R E H C P N =>
      [[BMark.b0],
        abelIdentityEncodeBHist Q,
        [BMark.b1, BMark.b0],
        abelIdentityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        abelIdentityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        abelIdentityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        abelIdentityEncodeBHist N]

private def abelIdentityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelIdentityEventAtDefault index rest

def abelIdentityFromEventFlow (ef : EventFlow) : Option AbelIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelIdentityUp.mk
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 1 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 3 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 5 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 7 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 9 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 11 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 13 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 15 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 17 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 19 ef))
      (abelIdentityDecodeBHist (abelIdentityEventAtDefault 21 ef)))

private theorem AbelIdentityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AbelIdentityUp,
      abelIdentityFromEventFlow (abelIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D W I S R E H C P N =>
      change
        some
          (AbelIdentityUp.mk
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist Q))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist D))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist W))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist I))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist S))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist R))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist E))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist H))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist C))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist P))
            (abelIdentityDecodeBHist (abelIdentityEncodeBHist N))) =
          some (AbelIdentityUp.mk Q D W I S R E H C P N)
      rw [AbelIdentityTasteGate_single_carrier_alignment_decode Q,
        AbelIdentityTasteGate_single_carrier_alignment_decode D,
        AbelIdentityTasteGate_single_carrier_alignment_decode W,
        AbelIdentityTasteGate_single_carrier_alignment_decode I,
        AbelIdentityTasteGate_single_carrier_alignment_decode S,
        AbelIdentityTasteGate_single_carrier_alignment_decode R,
        AbelIdentityTasteGate_single_carrier_alignment_decode E,
        AbelIdentityTasteGate_single_carrier_alignment_decode H,
        AbelIdentityTasteGate_single_carrier_alignment_decode C,
        AbelIdentityTasteGate_single_carrier_alignment_decode P,
        AbelIdentityTasteGate_single_carrier_alignment_decode N]

private theorem AbelIdentityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelIdentityUp} :
    abelIdentityToEventFlow x = abelIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelIdentityFromEventFlow (abelIdentityToEventFlow x) =
        abelIdentityFromEventFlow (abelIdentityToEventFlow y) :=
    congrArg abelIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbelIdentityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelIdentityTasteGate_single_carrier_alignment_round_trip y)))

instance abelIdentityBHistCarrier : BHistCarrier AbelIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelIdentityToEventFlow
  fromEventFlow := abelIdentityFromEventFlow

instance abelIdentityChapterTasteGate : ChapterTasteGate AbelIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelIdentityFromEventFlow (abelIdentityToEventFlow x) = some x
    exact AbelIdentityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelIdentityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate AbelIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelIdentityChapterTasteGate

theorem AbelIdentityTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier AbelIdentityUp) ∧
      Nonempty (ChapterTasteGate AbelIdentityUp) ∧
        (∀ h : BHist, abelIdentityDecodeBHist (abelIdentityEncodeBHist h) = h) ∧
          (∀ x : AbelIdentityUp,
            abelIdentityFromEventFlow (abelIdentityToEventFlow x) = some x) ∧
            abelIdentityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨abelIdentityBHistCarrier⟩,
      ⟨abelIdentityChapterTasteGate⟩,
      AbelIdentityTasteGate_single_carrier_alignment_decode,
      AbelIdentityTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.AbelIdentityUp.TasteGate
