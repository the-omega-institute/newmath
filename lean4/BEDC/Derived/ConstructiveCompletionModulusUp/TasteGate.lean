import BEDC.Derived.ConstructiveCompletionModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveCompletionModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def constructiveCompletionModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveCompletionModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveCompletionModulusEncodeBHist h

def constructiveCompletionModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveCompletionModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveCompletionModulusDecodeBHist tail)

private theorem constructiveCompletionModulusDecode_encode :
    forall h : BHist,
      constructiveCompletionModulusDecodeBHist (constructiveCompletionModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveCompletionModulusFields :
    ConstructiveCompletionModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveCompletionModulusUp.mk source modulus window readback dyadic realSeal
      transport replay provenance name =>
      [source, modulus, window, readback, dyadic, realSeal, transport, replay, provenance,
        name]

def constructiveCompletionModulusToEventFlow :
    ConstructiveCompletionModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveCompletionModulusUp.mk source modulus window readback dyadic realSeal
      transport replay provenance name =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        constructiveCompletionModulusEncodeBHist source,
        constructiveCompletionModulusEncodeBHist modulus,
        constructiveCompletionModulusEncodeBHist window,
        constructiveCompletionModulusEncodeBHist readback,
        constructiveCompletionModulusEncodeBHist dyadic,
        constructiveCompletionModulusEncodeBHist realSeal,
        constructiveCompletionModulusEncodeBHist transport,
        constructiveCompletionModulusEncodeBHist replay,
        constructiveCompletionModulusEncodeBHist provenance,
        constructiveCompletionModulusEncodeBHist name]

private def constructiveCompletionModulusEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      constructiveCompletionModulusEventAtDefault index rest

def constructiveCompletionModulusFromEventFlow
    (ef : EventFlow) : Option ConstructiveCompletionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveCompletionModulusUp.mk
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 1 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 2 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 3 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 4 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 5 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 6 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 7 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 8 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 9 ef))
      (constructiveCompletionModulusDecodeBHist
        (constructiveCompletionModulusEventAtDefault 10 ef)))

private theorem constructiveCompletionModulus_round_trip :
    forall x : ConstructiveCompletionModulusUp,
      constructiveCompletionModulusFromEventFlow
        (constructiveCompletionModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source modulus window readback dyadic realSeal transport replay provenance name =>
      change
        some
          (ConstructiveCompletionModulusUp.mk
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist source))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist modulus))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist window))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist readback))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist dyadic))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist realSeal))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist transport))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist replay))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist provenance))
            (constructiveCompletionModulusDecodeBHist
              (constructiveCompletionModulusEncodeBHist name))) =
          some
            (ConstructiveCompletionModulusUp.mk source modulus window readback dyadic
              realSeal transport replay provenance name)
      rw [constructiveCompletionModulusDecode_encode source,
        constructiveCompletionModulusDecode_encode modulus,
        constructiveCompletionModulusDecode_encode window,
        constructiveCompletionModulusDecode_encode readback,
        constructiveCompletionModulusDecode_encode dyadic,
        constructiveCompletionModulusDecode_encode realSeal,
        constructiveCompletionModulusDecode_encode transport,
        constructiveCompletionModulusDecode_encode replay,
        constructiveCompletionModulusDecode_encode provenance,
        constructiveCompletionModulusDecode_encode name]

private theorem constructiveCompletionModulusToEventFlow_injective
    {x y : ConstructiveCompletionModulusUp} :
    constructiveCompletionModulusToEventFlow x = constructiveCompletionModulusToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveCompletionModulusFromEventFlow
          (constructiveCompletionModulusToEventFlow x) =
        constructiveCompletionModulusFromEventFlow
          (constructiveCompletionModulusToEventFlow y) :=
    congrArg constructiveCompletionModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (constructiveCompletionModulus_round_trip x).symm
      (Eq.trans hread (constructiveCompletionModulus_round_trip y)))

private theorem constructiveCompletionModulus_fields_faithful :
    forall x y : ConstructiveCompletionModulusUp,
      constructiveCompletionModulusFields x = constructiveCompletionModulusFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 modulus1 window1 readback1 dyadic1 realSeal1 transport1 replay1
      provenance1 name1 =>
      cases y with
      | mk source2 modulus2 window2 readback2 dyadic2 realSeal2 transport2 replay2
          provenance2 name2 =>
          cases hfields
          rfl

instance constructiveCompletionModulusBHistCarrier :
    BHistCarrier ConstructiveCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveCompletionModulusToEventFlow
  fromEventFlow := constructiveCompletionModulusFromEventFlow

instance constructiveCompletionModulusChapterTasteGate :
    ChapterTasteGate ConstructiveCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveCompletionModulusFromEventFlow
        (constructiveCompletionModulusToEventFlow x) = some x
    exact constructiveCompletionModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveCompletionModulusToEventFlow_injective heq)

instance constructiveCompletionModulusFieldFaithful :
    FieldFaithful ConstructiveCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveCompletionModulusFields
  field_faithful := constructiveCompletionModulus_fields_faithful

instance constructiveCompletionModulusNontrivial :
    Nontrivial ConstructiveCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstructiveCompletionModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConstructiveCompletionModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConstructiveCompletionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveCompletionModulusChapterTasteGate

theorem ConstructiveCompletionModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveCompletionModulusDecodeBHist (constructiveCompletionModulusEncodeBHist h) =
        h) ∧
      (∀ x : ConstructiveCompletionModulusUp,
        constructiveCompletionModulusFromEventFlow
          (constructiveCompletionModulusToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveCompletionModulusUp,
          constructiveCompletionModulusToEventFlow x =
              constructiveCompletionModulusToEventFlow y ->
            x = y) ∧
          constructiveCompletionModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact constructiveCompletionModulusDecode_encode
  · constructor
    · exact constructiveCompletionModulus_round_trip
    · constructor
      · intro x y heq
        exact constructiveCompletionModulusToEventFlow_injective heq
      · rfl

end BEDC.Derived.ConstructiveCompletionModulusUp
