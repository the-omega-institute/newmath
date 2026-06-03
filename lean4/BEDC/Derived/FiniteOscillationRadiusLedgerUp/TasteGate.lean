import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteOscillationRadiusLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteOscillationRadiusLedgerUp : Type where
  | mk (K U A F B W R D S H C P N : BHist) : FiniteOscillationRadiusLedgerUp
  deriving DecidableEq

def finiteOscillationRadiusLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOscillationRadiusLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOscillationRadiusLedgerEncodeBHist h

def finiteOscillationRadiusLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOscillationRadiusLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOscillationRadiusLedgerDecodeBHist tail)

private theorem finiteOscillationRadiusLedgerDecodeEncodeBHist :
    ∀ h : BHist,
      finiteOscillationRadiusLedgerDecodeBHist
          (finiteOscillationRadiusLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteOscillationRadiusLedgerFields :
    FiniteOscillationRadiusLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOscillationRadiusLedgerUp.mk K U A F B W R D S H C P N =>
      [K, U, A, F, B, W, R, D, S, H, C, P, N]

def finiteOscillationRadiusLedgerToEventFlow :
    FiniteOscillationRadiusLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteOscillationRadiusLedgerFields x).map
      finiteOscillationRadiusLedgerEncodeBHist

def finiteOscillationRadiusLedgerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteOscillationRadiusLedgerEventAt index rest

def finiteOscillationRadiusLedgerFromEventFlow :
    EventFlow → Option FiniteOscillationRadiusLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (FiniteOscillationRadiusLedgerUp.mk
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 0 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 1 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 2 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 3 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 4 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 5 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 6 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 7 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 8 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 9 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 10 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 11 flow))
          (finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEventAt 12 flow)))

private theorem finiteOscillationRadiusLedger_round_trip :
    ∀ x : FiniteOscillationRadiusLedgerUp,
      finiteOscillationRadiusLedgerFromEventFlow
          (finiteOscillationRadiusLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K U A F B W R D S H C P N =>
      change
        some
          (FiniteOscillationRadiusLedgerUp.mk
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist K))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist U))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist A))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist F))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist B))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist W))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist R))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist D))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist S))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist H))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist C))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist P))
            (finiteOscillationRadiusLedgerDecodeBHist
              (finiteOscillationRadiusLedgerEncodeBHist N))) =
          some (FiniteOscillationRadiusLedgerUp.mk K U A F B W R D S H C P N)
      rw [finiteOscillationRadiusLedgerDecodeEncodeBHist K,
        finiteOscillationRadiusLedgerDecodeEncodeBHist U,
        finiteOscillationRadiusLedgerDecodeEncodeBHist A,
        finiteOscillationRadiusLedgerDecodeEncodeBHist F,
        finiteOscillationRadiusLedgerDecodeEncodeBHist B,
        finiteOscillationRadiusLedgerDecodeEncodeBHist W,
        finiteOscillationRadiusLedgerDecodeEncodeBHist R,
        finiteOscillationRadiusLedgerDecodeEncodeBHist D,
        finiteOscillationRadiusLedgerDecodeEncodeBHist S,
        finiteOscillationRadiusLedgerDecodeEncodeBHist H,
        finiteOscillationRadiusLedgerDecodeEncodeBHist C,
        finiteOscillationRadiusLedgerDecodeEncodeBHist P,
        finiteOscillationRadiusLedgerDecodeEncodeBHist N]

private theorem finiteOscillationRadiusLedgerToEventFlow_injective
    {x y : FiniteOscillationRadiusLedgerUp} :
    finiteOscillationRadiusLedgerToEventFlow x =
        finiteOscillationRadiusLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOscillationRadiusLedgerFromEventFlow
          (finiteOscillationRadiusLedgerToEventFlow x) =
        finiteOscillationRadiusLedgerFromEventFlow
          (finiteOscillationRadiusLedgerToEventFlow y) :=
    congrArg finiteOscillationRadiusLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteOscillationRadiusLedger_round_trip x).symm
      (Eq.trans hread (finiteOscillationRadiusLedger_round_trip y)))

private theorem finiteOscillationRadiusLedger_fields_faithful :
    ∀ x y : FiniteOscillationRadiusLedgerUp,
      finiteOscillationRadiusLedgerFields x =
          finiteOscillationRadiusLedgerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 U1 A1 F1 B1 W1 R1 D1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 U2 A2 F2 B2 W2 R2 D2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteOscillationRadiusLedgerBHistCarrier :
    BHistCarrier FiniteOscillationRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOscillationRadiusLedgerToEventFlow
  fromEventFlow := finiteOscillationRadiusLedgerFromEventFlow

instance finiteOscillationRadiusLedgerChapterTasteGate :
    ChapterTasteGate FiniteOscillationRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteOscillationRadiusLedgerFromEventFlow
          (finiteOscillationRadiusLedgerToEventFlow x) =
        some x
    exact finiteOscillationRadiusLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteOscillationRadiusLedgerToEventFlow_injective heq)

instance finiteOscillationRadiusLedgerFieldFaithful :
    FieldFaithful FiniteOscillationRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteOscillationRadiusLedgerFields
  field_faithful := finiteOscillationRadiusLedger_fields_faithful

instance finiteOscillationRadiusLedgerNontrivial :
    Nontrivial FiniteOscillationRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteOscillationRadiusLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteOscillationRadiusLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteOscillationRadiusLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteOscillationRadiusLedgerDecodeBHist
            (finiteOscillationRadiusLedgerEncodeBHist h) =
          h) ∧
      (∀ x : FiniteOscillationRadiusLedgerUp,
        finiteOscillationRadiusLedgerFromEventFlow
            (finiteOscillationRadiusLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteOscillationRadiusLedgerUp,
          finiteOscillationRadiusLedgerToEventFlow x =
              finiteOscillationRadiusLedgerToEventFlow y →
            x = y) ∧
          finiteOscillationRadiusLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact finiteOscillationRadiusLedgerDecodeEncodeBHist
  · constructor
    · exact finiteOscillationRadiusLedger_round_trip
    · constructor
      · intro x y heq
        exact finiteOscillationRadiusLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteOscillationRadiusLedgerUp
