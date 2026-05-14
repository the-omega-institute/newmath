import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalDiagonalSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalDiagonalSealUp : Type where
  | mk :
      (precision tail diagonal limit regular window dyadic sealRow transport route provenance name :
        BHist) →
      CofinalDiagonalSealUp
  deriving DecidableEq

def cofinalDiagonalSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalDiagonalSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalDiagonalSealEncodeBHist h

def cofinalDiagonalSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalDiagonalSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalDiagonalSealDecodeBHist tail)

private theorem cofinalDiagonalSeal_decode_encode_bhist :
    ∀ h : BHist,
      cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalDiagonalSealToEventFlow : CofinalDiagonalSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalDiagonalSealUp.mk precision tail diagonal limit regular window dyadic sealRow
      transport route provenance name =>
      [[BMark.b0],
        cofinalDiagonalSealEncodeBHist precision,
        [BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist limit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalDiagonalSealEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalDiagonalSealEncodeBHist name]

private def cofinalDiagonalSealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cofinalDiagonalSealRawAt n rest

private def cofinalDiagonalSealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cofinalDiagonalSealLengthEq n rest

def cofinalDiagonalSealFromEventFlow : EventFlow → Option CofinalDiagonalSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cofinalDiagonalSealLengthEq 24 flow with
      | true =>
          some
            (CofinalDiagonalSealUp.mk
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 1 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 3 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 5 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 7 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 9 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 11 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 13 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 15 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 17 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 19 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 21 flow))
              (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealRawAt 23 flow)))
      | false => none

private theorem cofinalDiagonalSeal_round_trip :
    ∀ x : CofinalDiagonalSealUp,
      cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision tail diagonal limit regular window dyadic sealRow transport route provenance name =>
      change
        some
          (CofinalDiagonalSealUp.mk
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist precision))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist tail))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist diagonal))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist limit))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist regular))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist window))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist dyadic))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist sealRow))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist transport))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist route))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist provenance))
            (cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist name))) =
          some
            (CofinalDiagonalSealUp.mk precision tail diagonal limit regular window dyadic sealRow
              transport route provenance name)
      rw [cofinalDiagonalSeal_decode_encode_bhist precision,
        cofinalDiagonalSeal_decode_encode_bhist tail,
        cofinalDiagonalSeal_decode_encode_bhist diagonal,
        cofinalDiagonalSeal_decode_encode_bhist limit,
        cofinalDiagonalSeal_decode_encode_bhist regular,
        cofinalDiagonalSeal_decode_encode_bhist window,
        cofinalDiagonalSeal_decode_encode_bhist dyadic,
        cofinalDiagonalSeal_decode_encode_bhist sealRow,
        cofinalDiagonalSeal_decode_encode_bhist transport,
        cofinalDiagonalSeal_decode_encode_bhist route,
        cofinalDiagonalSeal_decode_encode_bhist provenance,
        cofinalDiagonalSeal_decode_encode_bhist name]

private theorem cofinalDiagonalSealToEventFlow_injective {x y : CofinalDiagonalSealUp} :
    cofinalDiagonalSealToEventFlow x = cofinalDiagonalSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow x) =
        cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow y) :=
    congrArg cofinalDiagonalSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalDiagonalSeal_round_trip x).symm
      (Eq.trans hread (cofinalDiagonalSeal_round_trip y)))

instance cofinalDiagonalSealBHistCarrier : BHistCarrier CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalDiagonalSealToEventFlow
  fromEventFlow := cofinalDiagonalSealFromEventFlow

instance cofinalDiagonalSealChapterTasteGate : ChapterTasteGate CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalDiagonalSealFromEventFlow (cofinalDiagonalSealToEventFlow x) = some x
    exact cofinalDiagonalSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalDiagonalSealToEventFlow_injective heq)

instance cofinalDiagonalSealFieldFaithful : FieldFaithful CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CofinalDiagonalSealUp.mk precision tail diagonal limit regular window dyadic sealRow
        transport route provenance name =>
        [precision, tail, diagonal, limit, regular, window, dyadic, sealRow, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk precision1 tail1 diagonal1 limit1 regular1 window1 dyadic1 seal1 transport1 route1
        provenance1 name1 =>
        cases y with
        | mk precision2 tail2 diagonal2 limit2 regular2 window2 dyadic2 seal2 transport2 route2
            provenance2 name2 =>
            cases h
            rfl

instance cofinalDiagonalSealNontrivial : Nontrivial CofinalDiagonalSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalDiagonalSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalDiagonalSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CofinalDiagonalSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalDiagonalSealChapterTasteGate

theorem CofinalDiagonalSealTasteGate_single_carrier_alignment :
    ChapterTasteGate CofinalDiagonalSealUp ∧
      Nonempty (Nontrivial CofinalDiagonalSealUp) ∧
        Nonempty (FieldFaithful CofinalDiagonalSealUp) ∧
          (∀ h : BHist,
            cofinalDiagonalSealDecodeBHist (cofinalDiagonalSealEncodeBHist h) = h) ∧
            (∀ x y : CofinalDiagonalSealUp,
              cofinalDiagonalSealToEventFlow x = cofinalDiagonalSealToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cofinalDiagonalSealChapterTasteGate, ⟨cofinalDiagonalSealNontrivial⟩,
      ⟨cofinalDiagonalSealFieldFaithful⟩, cofinalDiagonalSeal_decode_encode_bhist,
      by
        intro x y heq
        exact cofinalDiagonalSealToEventFlow_injective heq⟩

end BEDC.Derived.CofinalDiagonalSealUp
