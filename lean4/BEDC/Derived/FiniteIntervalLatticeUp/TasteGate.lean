import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteIntervalLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteIntervalLatticeUp : Type where
  | mk
      (domain interval lower join meet split regular evidence history classifier
        provenance localName : BHist) : FiniteIntervalLatticeUp
  deriving DecidableEq

def finiteIntervalLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteIntervalLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteIntervalLatticeEncodeBHist h

def finiteIntervalLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteIntervalLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteIntervalLatticeDecodeBHist tail)

private theorem FiniteIntervalLatticeUp_decode :
    ∀ h : BHist,
      finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteIntervalLatticeFields : FiniteIntervalLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteIntervalLatticeUp.mk domain interval lower join meet split regular evidence
      history classifier provenance localName =>
      [domain, interval, lower, join, meet, split, regular, evidence, history,
        classifier, provenance, localName]

def finiteIntervalLatticeToEventFlow : FiniteIntervalLatticeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteIntervalLatticeFields x).map finiteIntervalLatticeEncodeBHist

private def finiteIntervalLatticeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteIntervalLatticeEventAtDefault index rest

def finiteIntervalLatticeFromEventFlow
    (ef : EventFlow) : Option FiniteIntervalLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteIntervalLatticeUp.mk
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 0 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 1 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 2 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 3 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 4 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 5 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 6 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 7 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 8 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 9 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 10 ef))
      (finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEventAtDefault 11 ef)))

private theorem FiniteIntervalLatticeUp_round_trip (x : FiniteIntervalLatticeUp) :
    finiteIntervalLatticeFromEventFlow (finiteIntervalLatticeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk domain interval lower join meet split regular evidence history classifier
      provenance localName =>
      change
        some
          (FiniteIntervalLatticeUp.mk
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist domain))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist interval))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist lower))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist join))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist meet))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist split))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist regular))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist evidence))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist history))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist classifier))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist provenance))
            (finiteIntervalLatticeDecodeBHist
              (finiteIntervalLatticeEncodeBHist localName))) =
          some
            (FiniteIntervalLatticeUp.mk domain interval lower join meet split regular
              evidence history classifier provenance localName)
      rw [FiniteIntervalLatticeUp_decode domain, FiniteIntervalLatticeUp_decode interval,
        FiniteIntervalLatticeUp_decode lower, FiniteIntervalLatticeUp_decode join,
        FiniteIntervalLatticeUp_decode meet, FiniteIntervalLatticeUp_decode split,
        FiniteIntervalLatticeUp_decode regular, FiniteIntervalLatticeUp_decode evidence,
        FiniteIntervalLatticeUp_decode history, FiniteIntervalLatticeUp_decode classifier,
        FiniteIntervalLatticeUp_decode provenance,
        FiniteIntervalLatticeUp_decode localName]

private theorem FiniteIntervalLatticeUp_toEventFlow_injective
    {x y : FiniteIntervalLatticeUp} :
    finiteIntervalLatticeToEventFlow x = finiteIntervalLatticeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteIntervalLatticeFromEventFlow (finiteIntervalLatticeToEventFlow x) =
        finiteIntervalLatticeFromEventFlow (finiteIntervalLatticeToEventFlow y) :=
    congrArg finiteIntervalLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteIntervalLatticeUp_round_trip x).symm
      (Eq.trans hread (FiniteIntervalLatticeUp_round_trip y)))

private theorem FiniteIntervalLatticeUp_fields :
    ∀ x y : FiniteIntervalLatticeUp,
      finiteIntervalLatticeFields x = finiteIntervalLatticeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk d1 i1 l1 j1 m1 s1 r1 e1 h1 c1 p1 n1 =>
      cases y with
      | mk d2 i2 l2 j2 m2 s2 r2 e2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance finiteIntervalLatticeBHistCarrier :
    BHistCarrier FiniteIntervalLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteIntervalLatticeToEventFlow
  fromEventFlow := finiteIntervalLatticeFromEventFlow

instance finiteIntervalLatticeChapterTasteGate :
    ChapterTasteGate FiniteIntervalLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteIntervalLatticeFromEventFlow (finiteIntervalLatticeToEventFlow x) =
      some x
    exact FiniteIntervalLatticeUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteIntervalLatticeUp_toEventFlow_injective heq)

instance finiteIntervalLatticeFieldFaithful :
    FieldFaithful FiniteIntervalLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteIntervalLatticeFields
  field_faithful := FiniteIntervalLatticeUp_fields

def taste_gate : ChapterTasteGate FiniteIntervalLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteIntervalLatticeChapterTasteGate

theorem FiniteIntervalLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteIntervalLatticeDecodeBHist (finiteIntervalLatticeEncodeBHist h) = h) ∧
      (∀ x : FiniteIntervalLatticeUp,
        finiteIntervalLatticeFromEventFlow (finiteIntervalLatticeToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteIntervalLatticeUp,
          finiteIntervalLatticeToEventFlow x = finiteIntervalLatticeToEventFlow y →
            x = y) ∧
          finiteIntervalLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FiniteIntervalLatticeUp_decode, FiniteIntervalLatticeUp_round_trip,
      fun x y heq => FiniteIntervalLatticeUp_toEventFlow_injective heq, rfl⟩

end BEDC.Derived.FiniteIntervalLatticeUp
