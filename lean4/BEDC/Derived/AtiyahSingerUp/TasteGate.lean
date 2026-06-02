import BEDC.Derived.AtiyahSingerUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AtiyahSingerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AtiyahSingerUp : Type where
  | mk
      (m operator symbol spectral analytic chern characteristic topological equality
        provenance : BHist) :
      AtiyahSingerUp
  deriving DecidableEq

def atiyahSingerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: atiyahSingerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: atiyahSingerEncodeBHist h

def atiyahSingerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (atiyahSingerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (atiyahSingerDecodeBHist tail)

private theorem AtiyahSingerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, atiyahSingerDecodeBHist (atiyahSingerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def atiyahSingerFields : AtiyahSingerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AtiyahSingerUp.mk m operator symbol spectral analytic chern characteristic topological
      equality provenance =>
      [m, operator, symbol, spectral, analytic, chern, characteristic, topological, equality,
        provenance]

def atiyahSingerToEventFlow : AtiyahSingerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (atiyahSingerFields x).map atiyahSingerEncodeBHist

private def atiyahSingerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => atiyahSingerEventAt index rest

def atiyahSingerFromEventFlow (ef : EventFlow) : Option AtiyahSingerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AtiyahSingerUp.mk
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 0 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 1 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 2 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 3 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 4 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 5 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 6 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 7 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 8 ef))
      (atiyahSingerDecodeBHist (atiyahSingerEventAt 9 ef)))

private theorem AtiyahSingerTasteGate_single_carrier_alignment_round_trip
    (x : AtiyahSingerUp) :
    atiyahSingerFromEventFlow (atiyahSingerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk m operator symbol spectral analytic chern characteristic topological equality
      provenance =>
      change
        some
          (AtiyahSingerUp.mk
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist m))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist operator))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist symbol))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist spectral))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist analytic))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist chern))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist characteristic))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist topological))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist equality))
            (atiyahSingerDecodeBHist (atiyahSingerEncodeBHist provenance))) =
          some
            (AtiyahSingerUp.mk m operator symbol spectral analytic chern characteristic
              topological equality provenance)
      rw [AtiyahSingerTasteGate_single_carrier_alignment_decode_encode m,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode operator,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode symbol,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode spectral,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode analytic,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode chern,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode characteristic,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode topological,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode equality,
        AtiyahSingerTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem AtiyahSingerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AtiyahSingerUp} :
    atiyahSingerToEventFlow x = atiyahSingerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      atiyahSingerFromEventFlow (atiyahSingerToEventFlow x) =
        atiyahSingerFromEventFlow (atiyahSingerToEventFlow y) :=
    congrArg atiyahSingerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AtiyahSingerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AtiyahSingerTasteGate_single_carrier_alignment_round_trip y)))

private theorem AtiyahSingerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AtiyahSingerUp, atiyahSingerFields x = atiyahSingerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk m₁ operator₁ symbol₁ spectral₁ analytic₁ chern₁ characteristic₁ topological₁
      equality₁ provenance₁ =>
      cases y with
      | mk m₂ operator₂ symbol₂ spectral₂ analytic₂ chern₂ characteristic₂ topological₂
          equality₂ provenance₂ =>
          cases hfields
          rfl

instance atiyahSingerBHistCarrier : BHistCarrier AtiyahSingerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := atiyahSingerToEventFlow
  fromEventFlow := atiyahSingerFromEventFlow

instance atiyahSingerChapterTasteGate : ChapterTasteGate AtiyahSingerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change atiyahSingerFromEventFlow (atiyahSingerToEventFlow x) = some x
    exact AtiyahSingerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AtiyahSingerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance atiyahSingerFieldFaithful : FieldFaithful AtiyahSingerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := atiyahSingerFields
  field_faithful := AtiyahSingerTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate AtiyahSingerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  atiyahSingerChapterTasteGate

theorem AtiyahSingerTasteGate_single_carrier_alignment :
    (∀ h : BHist, atiyahSingerDecodeBHist (atiyahSingerEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AtiyahSingerUp) ∧
        Nonempty (ChapterTasteGate AtiyahSingerUp) ∧
          atiyahSingerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AtiyahSingerTasteGate_single_carrier_alignment_decode_encode,
      ⟨atiyahSingerBHistCarrier⟩, ⟨atiyahSingerChapterTasteGate⟩, rfl⟩

end BEDC.Derived.AtiyahSingerUp
