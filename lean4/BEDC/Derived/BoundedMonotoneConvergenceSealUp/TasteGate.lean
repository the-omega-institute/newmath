import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedMonotoneConvergenceSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedMonotoneConvergenceSealUp : Type where
  | mk :
      (witness monotone criterion regSeq stream dyadic limitSeal realSeal transport route
        provenance nameCert : BHist) →
        BoundedMonotoneConvergenceSealUp
  deriving DecidableEq

def boundedMonotoneConvergenceSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedMonotoneConvergenceSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedMonotoneConvergenceSealEncodeBHist h

def boundedMonotoneConvergenceSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedMonotoneConvergenceSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedMonotoneConvergenceSealDecodeBHist tail)

private theorem boundedMonotoneConvergenceSeal_decode_encode_bhist :
    ∀ h : BHist,
      boundedMonotoneConvergenceSealDecodeBHist
        (boundedMonotoneConvergenceSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedMonotoneConvergenceSealToEventFlow :
    BoundedMonotoneConvergenceSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regSeq stream dyadic
      limitSeal realSeal transport route provenance nameCert =>
      [[BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist witness,
        [BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist monotone,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist criterion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist regSeq,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist nameCert]

private def boundedMonotoneConvergenceSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => boundedMonotoneConvergenceSealRawAt n rest

private def boundedMonotoneConvergenceSealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => boundedMonotoneConvergenceSealLengthEq n rest

def boundedMonotoneConvergenceSealFromEventFlow :
    EventFlow → Option BoundedMonotoneConvergenceSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match boundedMonotoneConvergenceSealLengthEq 24 flow with
      | true =>
          some
            (BoundedMonotoneConvergenceSealUp.mk
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 1 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 3 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 5 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 7 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 9 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 11 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 13 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 15 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 17 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 19 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 21 flow))
              (boundedMonotoneConvergenceSealDecodeBHist
                (boundedMonotoneConvergenceSealRawAt 23 flow)))
      | false => none

private theorem boundedMonotoneConvergenceSeal_round_trip :
    ∀ x : BoundedMonotoneConvergenceSealUp,
      boundedMonotoneConvergenceSealFromEventFlow
        (boundedMonotoneConvergenceSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk witness monotone criterion regSeq stream dyadic limitSeal realSeal transport route
      provenance nameCert =>
      change
        some
          (BoundedMonotoneConvergenceSealUp.mk
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist witness))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist monotone))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist criterion))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist regSeq))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist stream))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist dyadic))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist limitSeal))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist realSeal))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist transport))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist route))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist provenance))
            (boundedMonotoneConvergenceSealDecodeBHist
              (boundedMonotoneConvergenceSealEncodeBHist nameCert))) =
          some
            (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regSeq stream
              dyadic limitSeal realSeal transport route provenance nameCert)
      rw [boundedMonotoneConvergenceSeal_decode_encode_bhist witness,
        boundedMonotoneConvergenceSeal_decode_encode_bhist monotone,
        boundedMonotoneConvergenceSeal_decode_encode_bhist criterion,
        boundedMonotoneConvergenceSeal_decode_encode_bhist regSeq,
        boundedMonotoneConvergenceSeal_decode_encode_bhist stream,
        boundedMonotoneConvergenceSeal_decode_encode_bhist dyadic,
        boundedMonotoneConvergenceSeal_decode_encode_bhist limitSeal,
        boundedMonotoneConvergenceSeal_decode_encode_bhist realSeal,
        boundedMonotoneConvergenceSeal_decode_encode_bhist transport,
        boundedMonotoneConvergenceSeal_decode_encode_bhist route,
        boundedMonotoneConvergenceSeal_decode_encode_bhist provenance,
        boundedMonotoneConvergenceSeal_decode_encode_bhist nameCert]

private theorem boundedMonotoneConvergenceSealToEventFlow_injective
    {x y : BoundedMonotoneConvergenceSealUp} :
    boundedMonotoneConvergenceSealToEventFlow x =
      boundedMonotoneConvergenceSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedMonotoneConvergenceSealFromEventFlow
          (boundedMonotoneConvergenceSealToEventFlow x) =
        boundedMonotoneConvergenceSealFromEventFlow
          (boundedMonotoneConvergenceSealToEventFlow y) :=
    congrArg boundedMonotoneConvergenceSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedMonotoneConvergenceSeal_round_trip x).symm
      (Eq.trans hread (boundedMonotoneConvergenceSeal_round_trip y)))

instance boundedMonotoneConvergenceSealBHistCarrier :
    BHistCarrier BoundedMonotoneConvergenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedMonotoneConvergenceSealToEventFlow
  fromEventFlow := boundedMonotoneConvergenceSealFromEventFlow

instance boundedMonotoneConvergenceSealChapterTasteGate :
    ChapterTasteGate BoundedMonotoneConvergenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedMonotoneConvergenceSealFromEventFlow
        (boundedMonotoneConvergenceSealToEventFlow x) = some x
    exact boundedMonotoneConvergenceSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedMonotoneConvergenceSealToEventFlow_injective heq)

instance boundedMonotoneConvergenceSealFieldFaithful :
    FieldFaithful BoundedMonotoneConvergenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regSeq stream dyadic
        limitSeal realSeal transport route provenance nameCert =>
        [witness, monotone, criterion, regSeq, stream, dyadic, limitSeal, realSeal,
          transport, route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk witness1 monotone1 criterion1 regSeq1 stream1 dyadic1 limitSeal1 realSeal1
        transport1 route1 provenance1 nameCert1 =>
        cases y with
        | mk witness2 monotone2 criterion2 regSeq2 stream2 dyadic2 limitSeal2 realSeal2
            transport2 route2 provenance2 nameCert2 =>
            cases h
            rfl

instance boundedMonotoneConvergenceSealNontrivial :
    Nontrivial BoundedMonotoneConvergenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedMonotoneConvergenceSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedMonotoneConvergenceSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedMonotoneConvergenceSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedMonotoneConvergenceSealChapterTasteGate

theorem BoundedMonotoneConvergenceSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedMonotoneConvergenceSealDecodeBHist
        (boundedMonotoneConvergenceSealEncodeBHist h) = h) ∧
      (∀ x : BoundedMonotoneConvergenceSealUp,
        boundedMonotoneConvergenceSealFromEventFlow
          (boundedMonotoneConvergenceSealToEventFlow x) = some x) ∧
        (∀ x y : BoundedMonotoneConvergenceSealUp,
          boundedMonotoneConvergenceSealToEventFlow x =
            boundedMonotoneConvergenceSealToEventFlow y → x = y) ∧
          boundedMonotoneConvergenceSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨boundedMonotoneConvergenceSeal_decode_encode_bhist,
      boundedMonotoneConvergenceSeal_round_trip,
      by
        intro x y heq
        exact boundedMonotoneConvergenceSealToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BoundedMonotoneConvergenceSealUp
