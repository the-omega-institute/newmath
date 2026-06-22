import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformlyCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformlyCauchyFilterUp : Type where
  | mk (U L F N W D R E H C P Q : BHist) : UniformlyCauchyFilterUp
  deriving DecidableEq

def uniformlyCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformlyCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformlyCauchyFilterEncodeBHist h

def uniformlyCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformlyCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformlyCauchyFilterDecodeBHist tail)

private theorem uniformlyCauchyFilterDecode_encode_bhist :
    ∀ h : BHist,
      uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformlyCauchyFilterToEventFlow : UniformlyCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformlyCauchyFilterUp.mk U L F N W D R E H C P Q =>
      [uniformlyCauchyFilterEncodeBHist U,
        uniformlyCauchyFilterEncodeBHist L,
        uniformlyCauchyFilterEncodeBHist F,
        uniformlyCauchyFilterEncodeBHist N,
        uniformlyCauchyFilterEncodeBHist W,
        uniformlyCauchyFilterEncodeBHist D,
        uniformlyCauchyFilterEncodeBHist R,
        uniformlyCauchyFilterEncodeBHist E,
        uniformlyCauchyFilterEncodeBHist H,
        uniformlyCauchyFilterEncodeBHist C,
        uniformlyCauchyFilterEncodeBHist P,
        uniformlyCauchyFilterEncodeBHist Q]

private def uniformlyCauchyFilterRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => uniformlyCauchyFilterRawAt n rest

private def uniformlyCauchyFilterLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => uniformlyCauchyFilterLengthEq n rest

def uniformlyCauchyFilterFromEventFlow : EventFlow → Option UniformlyCauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match uniformlyCauchyFilterLengthEq 12 flow with
      | true =>
          some
            (UniformlyCauchyFilterUp.mk
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 0 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 1 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 2 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 3 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 4 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 5 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 6 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 7 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 8 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 9 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 10 flow))
              (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterRawAt 11 flow)))
      | false => none

private theorem uniformlyCauchyFilter_round_trip :
    ∀ x : UniformlyCauchyFilterUp,
      uniformlyCauchyFilterFromEventFlow (uniformlyCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U L F N W D R E H C P Q =>
      change
        some
          (UniformlyCauchyFilterUp.mk
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist U))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist L))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist F))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist N))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist W))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist D))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist R))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist E))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist H))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist C))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist P))
            (uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist Q))) =
          some (UniformlyCauchyFilterUp.mk U L F N W D R E H C P Q)
      rw [uniformlyCauchyFilterDecode_encode_bhist U,
        uniformlyCauchyFilterDecode_encode_bhist L,
        uniformlyCauchyFilterDecode_encode_bhist F,
        uniformlyCauchyFilterDecode_encode_bhist N,
        uniformlyCauchyFilterDecode_encode_bhist W,
        uniformlyCauchyFilterDecode_encode_bhist D,
        uniformlyCauchyFilterDecode_encode_bhist R,
        uniformlyCauchyFilterDecode_encode_bhist E,
        uniformlyCauchyFilterDecode_encode_bhist H,
        uniformlyCauchyFilterDecode_encode_bhist C,
        uniformlyCauchyFilterDecode_encode_bhist P,
        uniformlyCauchyFilterDecode_encode_bhist Q]

private theorem uniformlyCauchyFilterToEventFlow_injective {x y : UniformlyCauchyFilterUp} :
    uniformlyCauchyFilterToEventFlow x = uniformlyCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformlyCauchyFilterFromEventFlow (uniformlyCauchyFilterToEventFlow x) =
        uniformlyCauchyFilterFromEventFlow (uniformlyCauchyFilterToEventFlow y) :=
    congrArg uniformlyCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformlyCauchyFilter_round_trip x).symm
      (Eq.trans hread (uniformlyCauchyFilter_round_trip y)))

instance uniformlyCauchyFilterBHistCarrier : BHistCarrier UniformlyCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformlyCauchyFilterToEventFlow
  fromEventFlow := uniformlyCauchyFilterFromEventFlow

instance uniformlyCauchyFilterChapterTasteGate :
    ChapterTasteGate UniformlyCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformlyCauchyFilterFromEventFlow (uniformlyCauchyFilterToEventFlow x) = some x
    exact uniformlyCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformlyCauchyFilterToEventFlow_injective heq)

theorem UniformlyCauchyFilterTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformlyCauchyFilterDecodeBHist (uniformlyCauchyFilterEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformlyCauchyFilterUp) ∧
        Nonempty (ChapterTasteGate UniformlyCauchyFilterUp) ∧
          uniformlyCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨uniformlyCauchyFilterDecode_encode_bhist,
      ⟨uniformlyCauchyFilterBHistCarrier⟩,
      ⟨uniformlyCauchyFilterChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformlyCauchyFilterUp
