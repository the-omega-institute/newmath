import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowObserverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowObserverUp : Type where
  | mk (O F I K D H C P N : BHist) : FiniteWindowObserverUp
  deriving DecidableEq

def finiteWindowObserverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowObserverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowObserverEncodeBHist h

def finiteWindowObserverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowObserverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowObserverDecodeBHist tail)

private theorem finiteWindowObserver_decode_encode_bhist :
    ∀ h : BHist, finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteWindowObserverFields : FiniteWindowObserverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowObserverUp.mk O F I K D H C P N => [O, F, I, K, D, H, C, P, N]

def finiteWindowObserverToEventFlow : FiniteWindowObserverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowObserverUp.mk O F I K D H C P N =>
      [finiteWindowObserverEncodeBHist O,
        finiteWindowObserverEncodeBHist F,
        finiteWindowObserverEncodeBHist I,
        finiteWindowObserverEncodeBHist K,
        finiteWindowObserverEncodeBHist D,
        finiteWindowObserverEncodeBHist H,
        finiteWindowObserverEncodeBHist C,
        finiteWindowObserverEncodeBHist P,
        finiteWindowObserverEncodeBHist N]

private def finiteWindowObserverRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteWindowObserverRawAt n rest

private def finiteWindowObserverLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteWindowObserverLengthEq n rest

def finiteWindowObserverFromEventFlow : EventFlow → Option FiniteWindowObserverUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteWindowObserverLengthEq 9 flow with
      | true =>
          some
            (FiniteWindowObserverUp.mk
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 0 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 1 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 2 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 3 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 4 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 5 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 6 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 7 flow))
              (finiteWindowObserverDecodeBHist (finiteWindowObserverRawAt 8 flow)))
      | false => none

private theorem finiteWindowObserver_round_trip :
    ∀ x : FiniteWindowObserverUp,
      finiteWindowObserverFromEventFlow (finiteWindowObserverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O F I K D H C P N =>
      change
        some
          (FiniteWindowObserverUp.mk
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist O))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist F))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist I))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist K))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist D))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist H))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist C))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist P))
            (finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist N))) =
          some (FiniteWindowObserverUp.mk O F I K D H C P N)
      rw [finiteWindowObserver_decode_encode_bhist O,
        finiteWindowObserver_decode_encode_bhist F,
        finiteWindowObserver_decode_encode_bhist I,
        finiteWindowObserver_decode_encode_bhist K,
        finiteWindowObserver_decode_encode_bhist D,
        finiteWindowObserver_decode_encode_bhist H,
        finiteWindowObserver_decode_encode_bhist C,
        finiteWindowObserver_decode_encode_bhist P,
        finiteWindowObserver_decode_encode_bhist N]

private theorem finiteWindowObserverToEventFlow_injective {x y : FiniteWindowObserverUp} :
    finiteWindowObserverToEventFlow x = finiteWindowObserverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowObserverFromEventFlow (finiteWindowObserverToEventFlow x) =
        finiteWindowObserverFromEventFlow (finiteWindowObserverToEventFlow y) :=
    congrArg finiteWindowObserverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteWindowObserver_round_trip x).symm
      (Eq.trans hread (finiteWindowObserver_round_trip y)))

private theorem finiteWindowObserver_field_faithful :
    ∀ x y : FiniteWindowObserverUp,
      finiteWindowObserverFields x = finiteWindowObserverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk O1 F1 I1 K1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 F2 I2 K2 D2 H2 C2 P2 N2 =>
          cases h
          rfl

instance finiteWindowObserverBHistCarrier : BHistCarrier FiniteWindowObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowObserverToEventFlow
  fromEventFlow := finiteWindowObserverFromEventFlow

instance finiteWindowObserverChapterTasteGate :
    ChapterTasteGate FiniteWindowObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteWindowObserverFromEventFlow (finiteWindowObserverToEventFlow x) = some x
    exact finiteWindowObserver_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowObserverToEventFlow_injective heq)

instance finiteWindowObserverFieldFaithful : FieldFaithful FiniteWindowObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowObserverFields
  field_faithful := finiteWindowObserver_field_faithful

instance finiteWindowObserverNontrivial : Nontrivial FiniteWindowObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowObserverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowObserverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteWindowObserverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowObserverChapterTasteGate

theorem FiniteWindowObserverTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteWindowObserverDecodeBHist (finiteWindowObserverEncodeBHist h) = h) ∧
      (∀ x : FiniteWindowObserverUp,
        finiteWindowObserverFromEventFlow (finiteWindowObserverToEventFlow x) = some x) ∧
        (∀ x y : FiniteWindowObserverUp,
          finiteWindowObserverToEventFlow x = finiteWindowObserverToEventFlow y → x = y) ∧
          finiteWindowObserverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨finiteWindowObserver_decode_encode_bhist,
      finiteWindowObserver_round_trip,
      by
        intro x y heq
        exact finiteWindowObserverToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FiniteWindowObserverUp
