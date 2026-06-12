import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinderContextSubstitutionSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BinderContextSubstitutionSealUp : Type where
  | mk (term depth payload result boundary transport route provenance name : BHist) :
      BinderContextSubstitutionSealUp
  deriving DecidableEq

def binderContextSubstitutionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: binderContextSubstitutionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: binderContextSubstitutionSealEncodeBHist h

def binderContextSubstitutionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (binderContextSubstitutionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (binderContextSubstitutionSealDecodeBHist tail)

private theorem binderContextSubstitutionSeal_decode_encode_bhist :
    ∀ h : BHist,
      binderContextSubstitutionSealDecodeBHist
        (binderContextSubstitutionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def binderContextSubstitutionSealToEventFlow : BinderContextSubstitutionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BinderContextSubstitutionSealUp.mk term depth payload result boundary transport route
      provenance name =>
      [binderContextSubstitutionSealEncodeBHist term,
        binderContextSubstitutionSealEncodeBHist depth,
        binderContextSubstitutionSealEncodeBHist payload,
        binderContextSubstitutionSealEncodeBHist result,
        binderContextSubstitutionSealEncodeBHist boundary,
        binderContextSubstitutionSealEncodeBHist transport,
        binderContextSubstitutionSealEncodeBHist route,
        binderContextSubstitutionSealEncodeBHist provenance,
        binderContextSubstitutionSealEncodeBHist name]

private def binderContextSubstitutionSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, row :: _ => row
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => binderContextSubstitutionSealRawAt n rest

private def binderContextSubstitutionSealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => binderContextSubstitutionSealLengthEq n rest

def binderContextSubstitutionSealFromEventFlow :
    EventFlow → Option BinderContextSubstitutionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match binderContextSubstitutionSealLengthEq 9 flow with
      | true =>
          some
            (BinderContextSubstitutionSealUp.mk
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 0 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 1 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 2 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 3 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 4 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 5 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 6 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 7 flow))
              (binderContextSubstitutionSealDecodeBHist
                (binderContextSubstitutionSealRawAt 8 flow)))
      | false => none

private theorem binderContextSubstitutionSeal_round_trip :
    ∀ x : BinderContextSubstitutionSealUp,
      binderContextSubstitutionSealFromEventFlow
        (binderContextSubstitutionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term depth payload result boundary transport route provenance name =>
      change
        some
          (BinderContextSubstitutionSealUp.mk
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist term))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist depth))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist payload))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist result))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist boundary))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist transport))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist route))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist provenance))
            (binderContextSubstitutionSealDecodeBHist
              (binderContextSubstitutionSealEncodeBHist name))) =
          some
            (BinderContextSubstitutionSealUp.mk term depth payload result boundary transport
              route provenance name)
      rw [binderContextSubstitutionSeal_decode_encode_bhist term,
        binderContextSubstitutionSeal_decode_encode_bhist depth,
        binderContextSubstitutionSeal_decode_encode_bhist payload,
        binderContextSubstitutionSeal_decode_encode_bhist result,
        binderContextSubstitutionSeal_decode_encode_bhist boundary,
        binderContextSubstitutionSeal_decode_encode_bhist transport,
        binderContextSubstitutionSeal_decode_encode_bhist route,
        binderContextSubstitutionSeal_decode_encode_bhist provenance,
        binderContextSubstitutionSeal_decode_encode_bhist name]

private theorem binderContextSubstitutionSealToEventFlow_injective
    {x y : BinderContextSubstitutionSealUp} :
    binderContextSubstitutionSealToEventFlow x =
      binderContextSubstitutionSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      binderContextSubstitutionSealFromEventFlow
          (binderContextSubstitutionSealToEventFlow x) =
        binderContextSubstitutionSealFromEventFlow
          (binderContextSubstitutionSealToEventFlow y) :=
    congrArg binderContextSubstitutionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (binderContextSubstitutionSeal_round_trip x).symm
      (Eq.trans hread (binderContextSubstitutionSeal_round_trip y)))

instance binderContextSubstitutionSealBHistCarrier :
    BHistCarrier BinderContextSubstitutionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := binderContextSubstitutionSealToEventFlow
  fromEventFlow := binderContextSubstitutionSealFromEventFlow

instance binderContextSubstitutionSealChapterTasteGate :
    ChapterTasteGate BinderContextSubstitutionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      binderContextSubstitutionSealFromEventFlow
        (binderContextSubstitutionSealToEventFlow x) = some x
    exact binderContextSubstitutionSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (binderContextSubstitutionSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BinderContextSubstitutionSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  binderContextSubstitutionSealChapterTasteGate

theorem BinderContextSubstitutionSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      binderContextSubstitutionSealDecodeBHist
        (binderContextSubstitutionSealEncodeBHist h) = h) ∧
      (∀ x : BinderContextSubstitutionSealUp,
        binderContextSubstitutionSealFromEventFlow
          (binderContextSubstitutionSealToEventFlow x) = some x) ∧
        (∀ x y : BinderContextSubstitutionSealUp,
          binderContextSubstitutionSealToEventFlow x =
            binderContextSubstitutionSealToEventFlow y → x = y) ∧
          binderContextSubstitutionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨binderContextSubstitutionSeal_decode_encode_bhist,
      binderContextSubstitutionSeal_round_trip,
      by
        intro x y heq
        exact binderContextSubstitutionSealToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BinderContextSubstitutionSealUp
