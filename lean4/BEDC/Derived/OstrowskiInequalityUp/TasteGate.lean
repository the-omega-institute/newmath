import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OstrowskiInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OstrowskiInequalityUp : Type where
  | mk (I f x q W D A B R E H C P N : BHist) : OstrowskiInequalityUp
  deriving DecidableEq

def ostrowskiInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ostrowskiInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ostrowskiInequalityEncodeBHist h

def ostrowskiInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ostrowskiInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ostrowskiInequalityDecodeBHist tail)

private theorem ostrowskiInequality_decode_encode_bhist :
    ∀ h : BHist, ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ostrowskiInequalityFields : OstrowskiInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OstrowskiInequalityUp.mk I f x q W D A B R E H C P N =>
      [I, f, x, q, W, D, A, B, R, E, H, C, P, N]

def ostrowskiInequalityToEventFlow : OstrowskiInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | carrier => (ostrowskiInequalityFields carrier).map ostrowskiInequalityEncodeBHist

private def ostrowskiInequalityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ostrowskiInequalityEventAtDefault index rest

def ostrowskiInequalityFromEventFlow : EventFlow → Option OstrowskiInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (OstrowskiInequalityUp.mk
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 0 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 1 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 2 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 3 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 4 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 5 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 6 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 7 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 8 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 9 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 10 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 11 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 12 ef))
        (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEventAtDefault 13 ef)))

private theorem ostrowskiInequality_round_trip :
    ∀ carrier : OstrowskiInequalityUp,
      ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow carrier) =
        some carrier := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier
  cases carrier with
  | mk I f x q W D A B R E H C P N =>
      change
        some
          (OstrowskiInequalityUp.mk
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist I))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist f))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist x))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist q))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist W))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist D))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist A))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist B))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist R))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist E))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist H))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist C))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist P))
            (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist N))) =
          some (OstrowskiInequalityUp.mk I f x q W D A B R E H C P N)
      rw [ostrowskiInequality_decode_encode_bhist I,
        ostrowskiInequality_decode_encode_bhist f,
        ostrowskiInequality_decode_encode_bhist x,
        ostrowskiInequality_decode_encode_bhist q,
        ostrowskiInequality_decode_encode_bhist W,
        ostrowskiInequality_decode_encode_bhist D,
        ostrowskiInequality_decode_encode_bhist A,
        ostrowskiInequality_decode_encode_bhist B,
        ostrowskiInequality_decode_encode_bhist R,
        ostrowskiInequality_decode_encode_bhist E,
        ostrowskiInequality_decode_encode_bhist H,
        ostrowskiInequality_decode_encode_bhist C,
        ostrowskiInequality_decode_encode_bhist P,
        ostrowskiInequality_decode_encode_bhist N]

private theorem ostrowskiInequalityToEventFlow_injective {x y : OstrowskiInequalityUp} :
    ostrowskiInequalityToEventFlow x = ostrowskiInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow x) =
        ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow y) :=
    congrArg ostrowskiInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ostrowskiInequality_round_trip x).symm
      (Eq.trans hread (ostrowskiInequality_round_trip y)))

private theorem ostrowskiInequality_field_faithful :
    ∀ x y : OstrowskiInequalityUp,
      ostrowskiInequalityFields x = ostrowskiInequalityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ f₁ x₁ q₁ W₁ D₁ A₁ B₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ f₂ x₂ q₂ W₂ D₂ A₂ B₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance ostrowskiInequalityBHistCarrier : BHistCarrier OstrowskiInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ostrowskiInequalityToEventFlow
  fromEventFlow := ostrowskiInequalityFromEventFlow

instance ostrowskiInequalityChapterTasteGate : ChapterTasteGate OstrowskiInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow x) = some x
    exact ostrowskiInequality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ostrowskiInequalityToEventFlow_injective heq)

instance ostrowskiInequalityFieldFaithful : FieldFaithful OstrowskiInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  fields := ostrowskiInequalityFields
  field_faithful := ostrowskiInequality_field_faithful

instance ostrowskiInequalityNontrivial : Nontrivial OstrowskiInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OstrowskiInequalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      OstrowskiInequalityUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OstrowskiInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ostrowskiInequalityChapterTasteGate

theorem OstrowskiInequalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist h) = h) ∧
      (∀ x : OstrowskiInequalityUp,
        ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow x) = some x) ∧
        (∀ x y : OstrowskiInequalityUp,
          ostrowskiInequalityToEventFlow x = ostrowskiInequalityToEventFlow y -> x = y) ∧
          ostrowskiInequalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  have decode :
      ∀ h : BHist, ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have round :
      ∀ carrier : OstrowskiInequalityUp,
        ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow carrier) =
          some carrier := by
    intro carrier
    cases carrier with
    | mk I f x q W D A B R E H C P N =>
        change
          some
            (OstrowskiInequalityUp.mk
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist I))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist f))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist x))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist q))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist W))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist D))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist A))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist B))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist R))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist E))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist H))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist C))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist P))
              (ostrowskiInequalityDecodeBHist (ostrowskiInequalityEncodeBHist N))) =
            some (OstrowskiInequalityUp.mk I f x q W D A B R E H C P N)
        rw [decode I, decode f, decode x, decode q, decode W, decode D, decode A,
          decode B, decode R, decode E, decode H, decode C, decode P, decode N]
  have injective :
      ∀ x y : OstrowskiInequalityUp,
        ostrowskiInequalityToEventFlow x = ostrowskiInequalityToEventFlow y → x = y := by
    intro x y heq
    have hread :
        ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow x) =
          ostrowskiInequalityFromEventFlow (ostrowskiInequalityToEventFlow y) :=
      congrArg ostrowskiInequalityFromEventFlow heq
    exact Option.some.inj (Eq.trans (round x).symm (Eq.trans hread (round y)))
  exact
    ⟨decode, round, injective, rfl⟩

end BEDC.Derived.OstrowskiInequalityUp
