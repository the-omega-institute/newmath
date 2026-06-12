import BEDC.Derived.RealCauchyFilterMonadUnitUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyFilterMonadUnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realCauchyFilterMonadUnitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyFilterMonadUnitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyFilterMonadUnitEncodeBHist h

def realCauchyFilterMonadUnitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyFilterMonadUnitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyFilterMonadUnitDecodeBHist tail)

private theorem RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyFilterMonadUnitFields :
    BEDC.Derived.RealCauchyFilterMonadUnitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.RealCauchyFilterMonadUnitUp.packet
      real filterBase cauchyFilter completion universalProperty regSeq stream transport replay
      provenance name =>
      [real, filterBase, cauchyFilter, completion, universalProperty, regSeq, stream,
        transport, replay, provenance, name]

def realCauchyFilterMonadUnitToEventFlow :
    BEDC.Derived.RealCauchyFilterMonadUnitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCauchyFilterMonadUnitFields x).map realCauchyFilterMonadUnitEncodeBHist

private def realCauchyFilterMonadUnitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyFilterMonadUnitEventAt index rest

def realCauchyFilterMonadUnitFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.RealCauchyFilterMonadUnitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.RealCauchyFilterMonadUnitUp.packet
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 0 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 1 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 2 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 3 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 4 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 5 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 6 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 7 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 8 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 9 ef))
      (realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEventAt 10 ef)))

private theorem RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.RealCauchyFilterMonadUnitUp) :
    realCauchyFilterMonadUnitFromEventFlow (realCauchyFilterMonadUnitToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet real filterBase cauchyFilter completion universalProperty regSeq stream transport replay
      provenance name =>
      change
        some
          (BEDC.Derived.RealCauchyFilterMonadUnitUp.packet
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist real))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist filterBase))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist cauchyFilter))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist completion))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist universalProperty))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist regSeq))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist stream))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist transport))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist replay))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist provenance))
            (realCauchyFilterMonadUnitDecodeBHist
              (realCauchyFilterMonadUnitEncodeBHist name))) =
          some
            (BEDC.Derived.RealCauchyFilterMonadUnitUp.packet real filterBase cauchyFilter
              completion universalProperty regSeq stream transport replay provenance name)
      rw [RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode real,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode filterBase,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode cauchyFilter,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode completion,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode
          universalProperty,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode regSeq,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode stream,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode transport,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode replay,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode provenance,
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode name]

private theorem RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.RealCauchyFilterMonadUnitUp} :
    realCauchyFilterMonadUnitToEventFlow x = realCauchyFilterMonadUnitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyFilterMonadUnitFromEventFlow (realCauchyFilterMonadUnitToEventFlow x) =
        realCauchyFilterMonadUnitFromEventFlow (realCauchyFilterMonadUnitToEventFlow y) :=
    congrArg realCauchyFilterMonadUnitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BEDC.Derived.RealCauchyFilterMonadUnitUp,
      realCauchyFilterMonadUnitFields x = realCauchyFilterMonadUnitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet real₁ filterBase₁ cauchyFilter₁ completion₁ universalProperty₁ regSeq₁ stream₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | packet real₂ filterBase₂ cauchyFilter₂ completion₂ universalProperty₂ regSeq₂ stream₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance realCauchyFilterMonadUnitBHistCarrier :
    BHistCarrier BEDC.Derived.RealCauchyFilterMonadUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyFilterMonadUnitToEventFlow
  fromEventFlow := realCauchyFilterMonadUnitFromEventFlow

instance realCauchyFilterMonadUnitChapterTasteGate :
    ChapterTasteGate BEDC.Derived.RealCauchyFilterMonadUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCauchyFilterMonadUnitFromEventFlow
        (realCauchyFilterMonadUnitToEventFlow x) = some x
    exact RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realCauchyFilterMonadUnitFieldFaithful :
    FieldFaithful BEDC.Derived.RealCauchyFilterMonadUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCauchyFilterMonadUnitFields
  field_faithful :=
    RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_fields_faithful

instance realCauchyFilterMonadUnitNontrivial :
    Nontrivial BEDC.Derived.RealCauchyFilterMonadUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.RealCauchyFilterMonadUnitUp.packet (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BEDC.Derived.RealCauchyFilterMonadUnitUp.packet (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BEDC.Derived.RealCauchyFilterMonadUnitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyFilterMonadUnitChapterTasteGate

theorem RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCauchyFilterMonadUnitDecodeBHist (realCauchyFilterMonadUnitEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.RealCauchyFilterMonadUnitUp,
        realCauchyFilterMonadUnitFromEventFlow
          (realCauchyFilterMonadUnitToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.RealCauchyFilterMonadUnitUp,
          realCauchyFilterMonadUnitToEventFlow x =
            realCauchyFilterMonadUnitToEventFlow y → x = y) ∧
          realCauchyFilterMonadUnitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_decode_encode,
      RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealCauchyFilterMonadUnitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealCauchyFilterMonadUnitUp
