import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StolzCesaroTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StolzCesaroTheoremUp : Type where
  | mk (A D Q C R E H T P N : BHist) : StolzCesaroTheoremUp
  deriving DecidableEq

def stolzCesaroTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stolzCesaroTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stolzCesaroTheoremEncodeBHist h

def stolzCesaroTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stolzCesaroTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stolzCesaroTheoremDecodeBHist tail)

private theorem stolzCesaroTheorem_decode_encode_bhist :
    ∀ h : BHist,
      stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def stolzCesaroTheoremFields : StolzCesaroTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StolzCesaroTheoremUp.mk A D Q C R E H T P N => [A, D, Q, C, R, E, H, T, P, N]

def stolzCesaroTheoremToEventFlow :
    StolzCesaroTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (stolzCesaroTheoremFields x).map stolzCesaroTheoremEncodeBHist

private def stolzCesaroTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stolzCesaroTheoremEventAt index rest

def stolzCesaroTheoremFromEventFlow :
    EventFlow → Option StolzCesaroTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (StolzCesaroTheoremUp.mk
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 0 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 1 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 2 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 3 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 4 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 5 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 6 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 7 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 8 ef))
          (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEventAt 9 ef)))

private theorem stolzCesaroTheorem_round_trip :
    ∀ x : StolzCesaroTheoremUp,
      stolzCesaroTheoremFromEventFlow
        (stolzCesaroTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D Q C R E H T P N =>
      change
        some
          (StolzCesaroTheoremUp.mk
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist A))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist D))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist Q))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist C))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist R))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist E))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist H))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist T))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist P))
            (stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist N))) =
          some (StolzCesaroTheoremUp.mk A D Q C R E H T P N)
      rw [stolzCesaroTheorem_decode_encode_bhist A,
        stolzCesaroTheorem_decode_encode_bhist D,
        stolzCesaroTheorem_decode_encode_bhist Q,
        stolzCesaroTheorem_decode_encode_bhist C,
        stolzCesaroTheorem_decode_encode_bhist R,
        stolzCesaroTheorem_decode_encode_bhist E,
        stolzCesaroTheorem_decode_encode_bhist H,
        stolzCesaroTheorem_decode_encode_bhist T,
        stolzCesaroTheorem_decode_encode_bhist P,
        stolzCesaroTheorem_decode_encode_bhist N]

private theorem stolzCesaroTheoremToEventFlow_injective
    {x y : StolzCesaroTheoremUp} :
    stolzCesaroTheoremToEventFlow x =
        stolzCesaroTheoremToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stolzCesaroTheoremFromEventFlow (stolzCesaroTheoremToEventFlow x) =
        stolzCesaroTheoremFromEventFlow (stolzCesaroTheoremToEventFlow y) :=
    congrArg stolzCesaroTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stolzCesaroTheorem_round_trip x).symm
      (Eq.trans hread (stolzCesaroTheorem_round_trip y)))

private theorem stolzCesaroTheorem_field_faithful :
    ∀ x y : StolzCesaroTheoremUp,
      stolzCesaroTheoremFields x = stolzCesaroTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 D1 Q1 C1 R1 E1 H1 T1 P1 N1 =>
      cases y with
      | mk A2 D2 Q2 C2 R2 E2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance stolzCesaroTheoremBHistCarrier : BHistCarrier StolzCesaroTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stolzCesaroTheoremToEventFlow
  fromEventFlow := stolzCesaroTheoremFromEventFlow

instance stolzCesaroTheoremChapterTasteGate :
    ChapterTasteGate StolzCesaroTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stolzCesaroTheoremFromEventFlow (stolzCesaroTheoremToEventFlow x) = some x
    exact stolzCesaroTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stolzCesaroTheoremToEventFlow_injective heq)

instance stolzCesaroTheoremFieldFaithful :
    FieldFaithful StolzCesaroTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stolzCesaroTheoremFields
  field_faithful := stolzCesaroTheorem_field_faithful

instance stolzCesaroTheoremNontrivial :
    Nontrivial StolzCesaroTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StolzCesaroTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StolzCesaroTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StolzCesaroTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stolzCesaroTheoremChapterTasteGate

theorem StolzCesaroTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stolzCesaroTheoremDecodeBHist (stolzCesaroTheoremEncodeBHist h) = h) ∧
      (∀ x : StolzCesaroTheoremUp,
        stolzCesaroTheoremFromEventFlow
          (stolzCesaroTheoremToEventFlow x) = some x) ∧
        (∀ x y : StolzCesaroTheoremUp,
          stolzCesaroTheoremToEventFlow x = stolzCesaroTheoremToEventFlow y ->
            x = y) ∧
          stolzCesaroTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨stolzCesaroTheorem_decode_encode_bhist,
      stolzCesaroTheorem_round_trip,
      (fun _ _ heq => stolzCesaroTheoremToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StolzCesaroTheoremUp
