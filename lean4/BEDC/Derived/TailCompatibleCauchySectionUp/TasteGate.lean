import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailCompatibleCauchySectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailCompatibleCauchySectionUp : Type where
  | mk (family modulus precision index sectionRow window budget readback dyadic real transport
      replay provenance name : BHist) : TailCompatibleCauchySectionUp
  deriving DecidableEq

def tailCompatibleCauchySectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailCompatibleCauchySectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailCompatibleCauchySectionEncodeBHist h

def tailCompatibleCauchySectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailCompatibleCauchySectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailCompatibleCauchySectionDecodeBHist tail)

private theorem tailCompatibleCauchySection_decode_encode_bhist :
    ∀ h : BHist,
      tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tailCompatibleCauchySectionToEventFlow : TailCompatibleCauchySectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TailCompatibleCauchySectionUp.mk family modulus precision index sectionRow window budget
      readback dyadic real transport replay provenance name =>
      [[BMark.b0],
        tailCompatibleCauchySectionEncodeBHist family,
        [BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist index,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist sectionRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tailCompatibleCauchySectionEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist real,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist name]

private def tailCompatibleCauchySectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tailCompatibleCauchySectionEventAtDefault index rest

def tailCompatibleCauchySectionFromEventFlow
    (ef : EventFlow) : Option TailCompatibleCauchySectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TailCompatibleCauchySectionUp.mk
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 1 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 3 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 5 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 7 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 9 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 11 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 13 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 15 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 17 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 19 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 21 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 23 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 25 ef))
      (tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEventAtDefault 27 ef)))

private theorem tailCompatibleCauchySection_round_trip :
    ∀ x : TailCompatibleCauchySectionUp,
      tailCompatibleCauchySectionFromEventFlow
        (tailCompatibleCauchySectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family modulus precision index sectionRow window budget readback dyadic real transport
      replay provenance name =>
      change
        some
          (TailCompatibleCauchySectionUp.mk
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist family))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist modulus))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist precision))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist index))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist sectionRow))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist window))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist budget))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist readback))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist dyadic))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist real))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist transport))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist replay))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist provenance))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist name))) =
          some
            (TailCompatibleCauchySectionUp.mk family modulus precision index sectionRow window
              budget readback dyadic real transport replay provenance name)
      rw [tailCompatibleCauchySection_decode_encode_bhist family,
        tailCompatibleCauchySection_decode_encode_bhist modulus,
        tailCompatibleCauchySection_decode_encode_bhist precision,
        tailCompatibleCauchySection_decode_encode_bhist index,
        tailCompatibleCauchySection_decode_encode_bhist sectionRow,
        tailCompatibleCauchySection_decode_encode_bhist window,
        tailCompatibleCauchySection_decode_encode_bhist budget,
        tailCompatibleCauchySection_decode_encode_bhist readback,
        tailCompatibleCauchySection_decode_encode_bhist dyadic,
        tailCompatibleCauchySection_decode_encode_bhist real,
        tailCompatibleCauchySection_decode_encode_bhist transport,
        tailCompatibleCauchySection_decode_encode_bhist replay,
        tailCompatibleCauchySection_decode_encode_bhist provenance,
        tailCompatibleCauchySection_decode_encode_bhist name]

private theorem tailCompatibleCauchySectionToEventFlow_injective
    {x y : TailCompatibleCauchySectionUp} :
    tailCompatibleCauchySectionToEventFlow x = tailCompatibleCauchySectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tailCompatibleCauchySectionFromEventFlow
          (tailCompatibleCauchySectionToEventFlow x) =
        tailCompatibleCauchySectionFromEventFlow
          (tailCompatibleCauchySectionToEventFlow y) :=
    congrArg tailCompatibleCauchySectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tailCompatibleCauchySection_round_trip x).symm
      (Eq.trans hread (tailCompatibleCauchySection_round_trip y)))

private def tailCompatibleCauchySectionFields :
    TailCompatibleCauchySectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TailCompatibleCauchySectionUp.mk family modulus precision index sectionRow window budget
      readback dyadic real transport replay provenance name =>
      [family, modulus, precision, index, sectionRow, window, budget, readback, dyadic, real,
        transport, replay, provenance, name]

private theorem tailCompatibleCauchySection_field_faithful :
    ∀ x y : TailCompatibleCauchySectionUp,
      tailCompatibleCauchySectionFields x = tailCompatibleCauchySectionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk family₁ modulus₁ precision₁ index₁ sectionRow₁ window₁ budget₁ readback₁ dyadic₁
      real₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk family₂ modulus₂ precision₂ index₂ sectionRow₂ window₂ budget₂ readback₂ dyadic₂
          real₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance tailCompatibleCauchySectionBHistCarrier :
    BHistCarrier TailCompatibleCauchySectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailCompatibleCauchySectionToEventFlow
  fromEventFlow := tailCompatibleCauchySectionFromEventFlow

instance tailCompatibleCauchySectionChapterTasteGate :
    ChapterTasteGate TailCompatibleCauchySectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      tailCompatibleCauchySectionFromEventFlow
        (tailCompatibleCauchySectionToEventFlow x) = some x
    exact tailCompatibleCauchySection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tailCompatibleCauchySectionToEventFlow_injective heq)

instance tailCompatibleCauchySectionFieldFaithful :
    FieldFaithful TailCompatibleCauchySectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tailCompatibleCauchySectionFields
  field_faithful := tailCompatibleCauchySection_field_faithful

instance tailCompatibleCauchySectionNontrivial :
    Nontrivial TailCompatibleCauchySectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TailCompatibleCauchySectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TailCompatibleCauchySectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TailCompatibleCauchySectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tailCompatibleCauchySectionChapterTasteGate

theorem TailCompatibleCauchySectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate TailCompatibleCauchySectionUp) ∧
      (BHistCarrier.toEventFlow
          (TailCompatibleCauchySectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
        BHistCarrier.toEventFlow
          (TailCompatibleCauchySectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨tailCompatibleCauchySectionChapterTasteGate⟩
  · intro heq
    exact
      (tailCompatibleCauchySectionNontrivial.witness_pair.2.2
        (tailCompatibleCauchySectionToEventFlow_injective heq))

end BEDC.Derived.TailCompatibleCauchySectionUp
