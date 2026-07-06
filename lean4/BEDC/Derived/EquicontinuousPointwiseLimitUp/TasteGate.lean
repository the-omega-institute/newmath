import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuousPointwiseLimitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuousPointwiseLimitUp : Type where
  | mk (K F M W R A H C P N : BHist) : EquicontinuousPointwiseLimitUp
  deriving DecidableEq

def equicontinuousPointwiseLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuousPointwiseLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuousPointwiseLimitEncodeBHist h

def equicontinuousPointwiseLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuousPointwiseLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuousPointwiseLimitDecodeBHist tail)

private theorem equicontinuousPointwiseLimit_decode_encode_bhist :
    ∀ h : BHist,
      equicontinuousPointwiseLimitDecodeBHist
        (equicontinuousPointwiseLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def equicontinuousPointwiseLimitFields :
    EquicontinuousPointwiseLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuousPointwiseLimitUp.mk K F M W R A H C P N => [K, F, M, W, R, A, H, C, P, N]

def equicontinuousPointwiseLimitToEventFlow :
    EquicontinuousPointwiseLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (equicontinuousPointwiseLimitFields token).map
      equicontinuousPointwiseLimitEncodeBHist

private def equicontinuousPointwiseLimitRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => equicontinuousPointwiseLimitRawAt index rest

def equicontinuousPointwiseLimitFromEventFlow :
    EventFlow → Option EquicontinuousPointwiseLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (EquicontinuousPointwiseLimitUp.mk
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 0 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 1 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 2 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 3 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 4 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 5 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 6 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 7 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 8 flow))
          (equicontinuousPointwiseLimitDecodeBHist
            (equicontinuousPointwiseLimitRawAt 9 flow)))

private theorem equicontinuousPointwiseLimit_round_trip :
    ∀ x : EquicontinuousPointwiseLimitUp,
      equicontinuousPointwiseLimitFromEventFlow
        (equicontinuousPointwiseLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M W R A H C P N =>
      change
        some
          (EquicontinuousPointwiseLimitUp.mk
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist K))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist F))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist M))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist W))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist R))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist A))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist H))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist C))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist P))
            (equicontinuousPointwiseLimitDecodeBHist
              (equicontinuousPointwiseLimitEncodeBHist N))) =
          some (EquicontinuousPointwiseLimitUp.mk K F M W R A H C P N)
      rw [equicontinuousPointwiseLimit_decode_encode_bhist K,
        equicontinuousPointwiseLimit_decode_encode_bhist F,
        equicontinuousPointwiseLimit_decode_encode_bhist M,
        equicontinuousPointwiseLimit_decode_encode_bhist W,
        equicontinuousPointwiseLimit_decode_encode_bhist R,
        equicontinuousPointwiseLimit_decode_encode_bhist A,
        equicontinuousPointwiseLimit_decode_encode_bhist H,
        equicontinuousPointwiseLimit_decode_encode_bhist C,
        equicontinuousPointwiseLimit_decode_encode_bhist P,
        equicontinuousPointwiseLimit_decode_encode_bhist N]

private theorem equicontinuousPointwiseLimitToEventFlow_injective
    {x y : EquicontinuousPointwiseLimitUp} :
    equicontinuousPointwiseLimitToEventFlow x =
      equicontinuousPointwiseLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuousPointwiseLimitFromEventFlow
          (equicontinuousPointwiseLimitToEventFlow x) =
        equicontinuousPointwiseLimitFromEventFlow
          (equicontinuousPointwiseLimitToEventFlow y) :=
    congrArg equicontinuousPointwiseLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (equicontinuousPointwiseLimit_round_trip x).symm
      (Eq.trans hread (equicontinuousPointwiseLimit_round_trip y)))

instance equicontinuousPointwiseLimitBHistCarrier :
    BHistCarrier EquicontinuousPointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuousPointwiseLimitToEventFlow
  fromEventFlow := equicontinuousPointwiseLimitFromEventFlow

instance equicontinuousPointwiseLimitChapterTasteGate :
    ChapterTasteGate EquicontinuousPointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      equicontinuousPointwiseLimitFromEventFlow
        (equicontinuousPointwiseLimitToEventFlow x) = some x
    exact equicontinuousPointwiseLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (equicontinuousPointwiseLimitToEventFlow_injective heq)

theorem EquicontinuousPointwiseLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        equicontinuousPointwiseLimitDecodeBHist
          (equicontinuousPointwiseLimitEncodeBHist h) = h) ∧
      (∀ x : EquicontinuousPointwiseLimitUp,
        equicontinuousPointwiseLimitFromEventFlow
          (equicontinuousPointwiseLimitToEventFlow x) = some x) ∧
        (∀ x y : EquicontinuousPointwiseLimitUp,
          equicontinuousPointwiseLimitToEventFlow x =
            equicontinuousPointwiseLimitToEventFlow y → x = y) ∧
          equicontinuousPointwiseLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨equicontinuousPointwiseLimit_decode_encode_bhist,
      equicontinuousPointwiseLimit_round_trip,
      (fun _ _ heq => equicontinuousPointwiseLimitToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EquicontinuousPointwiseLimitUp.TasteGate
