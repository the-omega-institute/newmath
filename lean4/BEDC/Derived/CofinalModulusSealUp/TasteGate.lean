import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalModulusSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalModulusSealUp : Type where
  | mk (budget modulus window limit regSeq stream dyadic real transport replay provenance
      name : BHist) : CofinalModulusSealUp
  deriving DecidableEq

def cofinalModulusSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalModulusSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalModulusSealEncodeBHist h

def cofinalModulusSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalModulusSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalModulusSealDecodeBHist tail)

private theorem cofinalModulusSeal_decode_encode_bhist :
    ∀ h : BHist, cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cofinalModulusSealToEventFlow : CofinalModulusSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real transport
      replay provenance name =>
      [[BMark.b0],
        cofinalModulusSealEncodeBHist budget,
        [BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist limit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist regSeq,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalModulusSealEncodeBHist real,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusSealEncodeBHist name]

private def cofinalModulusSealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cofinalModulusSealEventAtDefault index rest

def cofinalModulusSealFromEventFlow (ef : EventFlow) : Option CofinalModulusSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CofinalModulusSealUp.mk
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 1 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 3 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 5 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 7 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 9 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 11 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 13 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 15 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 17 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 19 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 21 ef))
      (cofinalModulusSealDecodeBHist (cofinalModulusSealEventAtDefault 23 ef)))

private theorem cofinalModulusSeal_round_trip :
    ∀ x : CofinalModulusSealUp,
      cofinalModulusSealFromEventFlow (cofinalModulusSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk budget modulus window limit regSeq stream dyadic real transport replay provenance name =>
      change
        some
          (CofinalModulusSealUp.mk
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist budget))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist modulus))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist window))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist limit))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist regSeq))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist stream))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist dyadic))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist real))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist transport))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist replay))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist provenance))
            (cofinalModulusSealDecodeBHist (cofinalModulusSealEncodeBHist name))) =
          some
            (CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
              transport replay provenance name)
      rw [cofinalModulusSeal_decode_encode_bhist budget,
        cofinalModulusSeal_decode_encode_bhist modulus,
        cofinalModulusSeal_decode_encode_bhist window,
        cofinalModulusSeal_decode_encode_bhist limit,
        cofinalModulusSeal_decode_encode_bhist regSeq,
        cofinalModulusSeal_decode_encode_bhist stream,
        cofinalModulusSeal_decode_encode_bhist dyadic,
        cofinalModulusSeal_decode_encode_bhist real,
        cofinalModulusSeal_decode_encode_bhist transport,
        cofinalModulusSeal_decode_encode_bhist replay,
        cofinalModulusSeal_decode_encode_bhist provenance,
        cofinalModulusSeal_decode_encode_bhist name]

private theorem cofinalModulusSealToEventFlow_injective {x y : CofinalModulusSealUp} :
    cofinalModulusSealToEventFlow x = cofinalModulusSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalModulusSealFromEventFlow (cofinalModulusSealToEventFlow x) =
        cofinalModulusSealFromEventFlow (cofinalModulusSealToEventFlow y) :=
    congrArg cofinalModulusSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalModulusSeal_round_trip x).symm
      (Eq.trans hread (cofinalModulusSeal_round_trip y)))

private def cofinalModulusSealFields : CofinalModulusSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real transport
      replay provenance name =>
      [budget, modulus, window, limit, regSeq, stream, dyadic, real, transport, replay,
        provenance, name]

private theorem cofinalModulusSeal_field_faithful :
    ∀ x y : CofinalModulusSealUp, cofinalModulusSealFields x = cofinalModulusSealFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk budget₁ modulus₁ window₁ limit₁ regSeq₁ stream₁ dyadic₁ real₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk budget₂ modulus₂ window₂ limit₂ regSeq₂ stream₂ dyadic₂ real₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases hfields
          rfl

instance cofinalModulusSealBHistCarrier : BHistCarrier CofinalModulusSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalModulusSealToEventFlow
  fromEventFlow := cofinalModulusSealFromEventFlow

instance cofinalModulusSealChapterTasteGate : ChapterTasteGate CofinalModulusSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalModulusSealFromEventFlow (cofinalModulusSealToEventFlow x) = some x
    exact cofinalModulusSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalModulusSealToEventFlow_injective heq)

instance cofinalModulusSealFieldFaithful : FieldFaithful CofinalModulusSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalModulusSealFields
  field_faithful := cofinalModulusSeal_field_faithful

instance cofinalModulusSealNontrivial : Nontrivial CofinalModulusSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalModulusSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalModulusSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CofinalModulusSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalModulusSealChapterTasteGate

theorem CofinalModulusSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CofinalModulusSealUp) ∧
      (BHistCarrier.toEventFlow
          (CofinalModulusSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) ≠
        BHistCarrier.toEventFlow
          (CofinalModulusSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cofinalModulusSealChapterTasteGate⟩
  · intro heq
    exact
      (cofinalModulusSealNontrivial.witness_pair.2.2
        (cofinalModulusSealToEventFlow_injective heq))

end BEDC.Derived.CofinalModulusSealUp
