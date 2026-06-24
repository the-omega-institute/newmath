import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySeparatedReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySeparatedReflectionUp : Type where
  | mk (A R M Z E H C P N : BHist) : CauchySeparatedReflectionUp
  deriving DecidableEq

def cauchySeparatedReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySeparatedReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySeparatedReflectionEncodeBHist h

def cauchySeparatedReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySeparatedReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySeparatedReflectionDecodeBHist tail)

private theorem cauchySeparatedReflection_decode_encode_bhist :
    ∀ h : BHist,
      cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySeparatedReflectionFields :
    CauchySeparatedReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySeparatedReflectionUp.mk A R M Z E H C P N => [A, R, M, Z, E, H, C, P, N]

def cauchySeparatedReflectionToEventFlow :
    CauchySeparatedReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySeparatedReflectionFields x).map cauchySeparatedReflectionEncodeBHist

private def cauchySeparatedReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySeparatedReflectionEventAtDefault index rest

def cauchySeparatedReflectionFromEventFlow
    (ef : EventFlow) : Option CauchySeparatedReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySeparatedReflectionUp.mk
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 0 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 1 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 2 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 3 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 4 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 5 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 6 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 7 ef))
      (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEventAtDefault 8 ef)))

private theorem cauchySeparatedReflection_round_trip :
    ∀ x : CauchySeparatedReflectionUp,
      cauchySeparatedReflectionFromEventFlow (cauchySeparatedReflectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A R M Z E H C P N =>
      change
        some
          (CauchySeparatedReflectionUp.mk
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist A))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist R))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist M))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist Z))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist E))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist H))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist C))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist P))
            (cauchySeparatedReflectionDecodeBHist (cauchySeparatedReflectionEncodeBHist N))) =
          some (CauchySeparatedReflectionUp.mk A R M Z E H C P N)
      rw [cauchySeparatedReflection_decode_encode_bhist A,
        cauchySeparatedReflection_decode_encode_bhist R,
        cauchySeparatedReflection_decode_encode_bhist M,
        cauchySeparatedReflection_decode_encode_bhist Z,
        cauchySeparatedReflection_decode_encode_bhist E,
        cauchySeparatedReflection_decode_encode_bhist H,
        cauchySeparatedReflection_decode_encode_bhist C,
        cauchySeparatedReflection_decode_encode_bhist P,
        cauchySeparatedReflection_decode_encode_bhist N]

private theorem cauchySeparatedReflectionToEventFlow_injective
    {x y : CauchySeparatedReflectionUp} :
    cauchySeparatedReflectionToEventFlow x = cauchySeparatedReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySeparatedReflectionFromEventFlow (cauchySeparatedReflectionToEventFlow x) =
        cauchySeparatedReflectionFromEventFlow (cauchySeparatedReflectionToEventFlow y) :=
    congrArg cauchySeparatedReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySeparatedReflection_round_trip x).symm
      (Eq.trans hread (cauchySeparatedReflection_round_trip y)))

private theorem cauchySeparatedReflection_field_faithful :
    ∀ x y : CauchySeparatedReflectionUp,
      cauchySeparatedReflectionFields x = cauchySeparatedReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A R M Z E H C P N =>
      cases y with
      | mk A' R' M' Z' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchySeparatedReflectionBHistCarrier :
    BHistCarrier CauchySeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySeparatedReflectionToEventFlow
  fromEventFlow := cauchySeparatedReflectionFromEventFlow

instance cauchySeparatedReflectionChapterTasteGate :
    ChapterTasteGate CauchySeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySeparatedReflectionFromEventFlow
      (cauchySeparatedReflectionToEventFlow x) = some x
    exact cauchySeparatedReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySeparatedReflectionToEventFlow_injective heq)

instance cauchySeparatedReflectionFieldFaithful :
    FieldFaithful CauchySeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySeparatedReflectionFields
  field_faithful := cauchySeparatedReflection_field_faithful

instance cauchySeparatedReflectionNontrivial :
    Nontrivial CauchySeparatedReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySeparatedReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySeparatedReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySeparatedReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySeparatedReflectionChapterTasteGate

theorem CauchySeparatedReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySeparatedReflectionDecodeBHist
      (cauchySeparatedReflectionEncodeBHist h) = h) ∧
      (∀ x : CauchySeparatedReflectionUp,
        cauchySeparatedReflectionFromEventFlow (cauchySeparatedReflectionToEventFlow x) =
          some x) ∧
        (∀ x y : CauchySeparatedReflectionUp,
          cauchySeparatedReflectionToEventFlow x = cauchySeparatedReflectionToEventFlow y →
            x = y) ∧
          cauchySeparatedReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact cauchySeparatedReflection_decode_encode_bhist
  · constructor
    · exact cauchySeparatedReflection_round_trip
    · constructor
      · intro x y heq
        exact cauchySeparatedReflectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchySeparatedReflectionUp
