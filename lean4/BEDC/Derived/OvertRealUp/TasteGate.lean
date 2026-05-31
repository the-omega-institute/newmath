import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OvertRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OvertRealUp : Type where
  | mk
      (realSeal interval cover lower upper witness antiEscape transport replay provenance
        name : BHist) :
      OvertRealUp
  deriving DecidableEq

def overtRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: overtRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: overtRealEncodeBHist h

def overtRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (overtRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (overtRealDecodeBHist tail)

private theorem overtReal_decode_encode_bhist :
    ∀ h : BHist, overtRealDecodeBHist (overtRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def overtRealFields : OvertRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OvertRealUp.mk realSeal interval cover lower upper witness antiEscape transport replay
      provenance name =>
      [realSeal, interval, cover, lower, upper, witness, antiEscape, transport, replay,
        provenance, name]

def overtRealToEventFlow : OvertRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (overtRealFields x).map overtRealEncodeBHist

private def overtRealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => overtRealRawAt index rest

def overtRealFromEventFlow (flow : EventFlow) : Option OvertRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OvertRealUp.mk
      (overtRealDecodeBHist (overtRealRawAt 0 flow))
      (overtRealDecodeBHist (overtRealRawAt 1 flow))
      (overtRealDecodeBHist (overtRealRawAt 2 flow))
      (overtRealDecodeBHist (overtRealRawAt 3 flow))
      (overtRealDecodeBHist (overtRealRawAt 4 flow))
      (overtRealDecodeBHist (overtRealRawAt 5 flow))
      (overtRealDecodeBHist (overtRealRawAt 6 flow))
      (overtRealDecodeBHist (overtRealRawAt 7 flow))
      (overtRealDecodeBHist (overtRealRawAt 8 flow))
      (overtRealDecodeBHist (overtRealRawAt 9 flow))
      (overtRealDecodeBHist (overtRealRawAt 10 flow)))

private theorem overtReal_round_trip :
    ∀ x : OvertRealUp, overtRealFromEventFlow (overtRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk realSeal interval cover lower upper witness antiEscape transport replay provenance name =>
      change
        some
          (OvertRealUp.mk
            (overtRealDecodeBHist (overtRealEncodeBHist realSeal))
            (overtRealDecodeBHist (overtRealEncodeBHist interval))
            (overtRealDecodeBHist (overtRealEncodeBHist cover))
            (overtRealDecodeBHist (overtRealEncodeBHist lower))
            (overtRealDecodeBHist (overtRealEncodeBHist upper))
            (overtRealDecodeBHist (overtRealEncodeBHist witness))
            (overtRealDecodeBHist (overtRealEncodeBHist antiEscape))
            (overtRealDecodeBHist (overtRealEncodeBHist transport))
            (overtRealDecodeBHist (overtRealEncodeBHist replay))
            (overtRealDecodeBHist (overtRealEncodeBHist provenance))
            (overtRealDecodeBHist (overtRealEncodeBHist name))) =
          some
            (OvertRealUp.mk realSeal interval cover lower upper witness antiEscape transport
              replay provenance name)
      rw [overtReal_decode_encode_bhist realSeal, overtReal_decode_encode_bhist interval,
        overtReal_decode_encode_bhist cover, overtReal_decode_encode_bhist lower,
        overtReal_decode_encode_bhist upper, overtReal_decode_encode_bhist witness,
        overtReal_decode_encode_bhist antiEscape, overtReal_decode_encode_bhist transport,
        overtReal_decode_encode_bhist replay, overtReal_decode_encode_bhist provenance,
        overtReal_decode_encode_bhist name]

private theorem overtRealToEventFlow_injective {x y : OvertRealUp} :
    overtRealToEventFlow x = overtRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      overtRealFromEventFlow (overtRealToEventFlow x) =
        overtRealFromEventFlow (overtRealToEventFlow y) :=
    congrArg overtRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (overtReal_round_trip x).symm (Eq.trans hread (overtReal_round_trip y)))

private theorem overtReal_fields_faithful :
    ∀ x y : OvertRealUp, overtRealFields x = overtRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk r₁ i₁ c₁ l₁ u₁ w₁ a₁ h₁ t₁ p₁ n₁ =>
      cases y with
      | mk r₂ i₂ c₂ l₂ u₂ w₂ a₂ h₂ t₂ p₂ n₂ =>
          cases hfields
          rfl

instance overtRealBHistCarrier : BHistCarrier OvertRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := overtRealToEventFlow
  fromEventFlow := overtRealFromEventFlow

instance overtRealChapterTasteGate : ChapterTasteGate OvertRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change overtRealFromEventFlow (overtRealToEventFlow x) = some x
    exact overtReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (overtRealToEventFlow_injective heq)

instance overtRealFieldFaithful : FieldFaithful OvertRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := overtRealFields
  field_faithful := overtReal_fields_faithful

instance overtRealNontrivial : Nontrivial OvertRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OvertRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OvertRealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem OvertRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate OvertRealUp) ∧
      Nonempty (FieldFaithful OvertRealUp) ∧
        Nonempty (Nontrivial OvertRealUp) ∧
          (∃ x : OvertRealUp,
            FieldFaithful.fields x =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨overtRealChapterTasteGate⟩,
      ⟨⟨overtRealFieldFaithful⟩,
        ⟨⟨overtRealNontrivial⟩,
          ⟨OvertRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            rfl⟩⟩⟩⟩

end BEDC.Derived.OvertRealUp
