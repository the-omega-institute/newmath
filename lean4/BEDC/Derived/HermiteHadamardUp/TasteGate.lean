import BEDC.Derived.HermiteHadamardUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HermiteHadamardUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def hermiteHadamardEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hermiteHadamardEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hermiteHadamardEncodeBHist h

def hermiteHadamardDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hermiteHadamardDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hermiteHadamardDecodeBHist tail)

private theorem HermiteHadamardTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hermiteHadamardFields : BEDC.Derived.HermiteHadamardUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.HermiteHadamardUp.mk
      function interval midpoint average jensen karamata comparison endpoint transport replay
      provenance name =>
      [function, interval, midpoint, average, jensen, karamata, comparison, endpoint, transport,
        replay, provenance, name]

def hermiteHadamardToEventFlow : BEDC.Derived.HermiteHadamardUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hermiteHadamardFields x).map hermiteHadamardEncodeBHist

private def hermiteHadamardEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hermiteHadamardEventAt index rest

def hermiteHadamardFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.HermiteHadamardUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.HermiteHadamardUp.mk
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 0 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 1 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 2 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 3 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 4 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 5 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 6 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 7 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 8 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 9 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 10 ef))
      (hermiteHadamardDecodeBHist (hermiteHadamardEventAt 11 ef)))

private theorem HermiteHadamardTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.HermiteHadamardUp) :
    hermiteHadamardFromEventFlow (hermiteHadamardToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk function interval midpoint average jensen karamata comparison endpoint transport replay
      provenance name =>
      change
        some
          (BEDC.Derived.HermiteHadamardUp.mk
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist function))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist interval))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist midpoint))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist average))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist jensen))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist karamata))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist comparison))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist endpoint))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist transport))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist replay))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist provenance))
            (hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist name))) =
          some
            (BEDC.Derived.HermiteHadamardUp.mk function interval midpoint average jensen
              karamata comparison endpoint transport replay provenance name)
      rw [HermiteHadamardTasteGate_single_carrier_alignment_decode_encode function,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode interval,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode midpoint,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode average,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode jensen,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode karamata,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode comparison,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode endpoint,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode transport,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode replay,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode provenance,
        HermiteHadamardTasteGate_single_carrier_alignment_decode_encode name]

private theorem HermiteHadamardTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.HermiteHadamardUp} :
    hermiteHadamardToEventFlow x = hermiteHadamardToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hermiteHadamardFromEventFlow (hermiteHadamardToEventFlow x) =
        hermiteHadamardFromEventFlow (hermiteHadamardToEventFlow y) :=
    congrArg hermiteHadamardFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HermiteHadamardTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HermiteHadamardTasteGate_single_carrier_alignment_round_trip y)))

private theorem HermiteHadamardTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BEDC.Derived.HermiteHadamardUp,
      hermiteHadamardFields x = hermiteHadamardFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk function₁ interval₁ midpoint₁ average₁ jensen₁ karamata₁ comparison₁ endpoint₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk function₂ interval₂ midpoint₂ average₂ jensen₂ karamata₂ comparison₂ endpoint₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance hermiteHadamardBHistCarrier : BHistCarrier BEDC.Derived.HermiteHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hermiteHadamardToEventFlow
  fromEventFlow := hermiteHadamardFromEventFlow

instance hermiteHadamardChapterTasteGate :
    ChapterTasteGate BEDC.Derived.HermiteHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hermiteHadamardFromEventFlow (hermiteHadamardToEventFlow x) = some x
    exact HermiteHadamardTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HermiteHadamardTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hermiteHadamardFieldFaithful : FieldFaithful BEDC.Derived.HermiteHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hermiteHadamardFields
  field_faithful := HermiteHadamardTasteGate_single_carrier_alignment_fields_faithful

instance hermiteHadamardNontrivial : Nontrivial BEDC.Derived.HermiteHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.HermiteHadamardUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BEDC.Derived.HermiteHadamardUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HermiteHadamardTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BEDC.Derived.HermiteHadamardUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hermiteHadamardChapterTasteGate

theorem HermiteHadamardTasteGate_single_carrier_alignment :
    (∀ h : BHist, hermiteHadamardDecodeBHist (hermiteHadamardEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.HermiteHadamardUp,
        hermiteHadamardFromEventFlow (hermiteHadamardToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.HermiteHadamardUp,
          hermiteHadamardToEventFlow x = hermiteHadamardToEventFlow y → x = y) ∧
          hermiteHadamardEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HermiteHadamardTasteGate_single_carrier_alignment_decode_encode,
      HermiteHadamardTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HermiteHadamardTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HermiteHadamardUp
