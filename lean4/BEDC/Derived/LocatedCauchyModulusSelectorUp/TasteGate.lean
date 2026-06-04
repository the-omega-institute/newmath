import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyModulusSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyModulusSelectorUp : Type where
  | mk
      (domain window rational modulus located evidence history classifier provenance
        localName : BHist) : LocatedCauchyModulusSelectorUp
  deriving DecidableEq

def locatedCauchyModulusSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyModulusSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyModulusSelectorEncodeBHist h

def locatedCauchyModulusSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyModulusSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyModulusSelectorDecodeBHist tail)

private theorem LocatedCauchyModulusSelectorUp_decode :
    ∀ h : BHist,
      locatedCauchyModulusSelectorDecodeBHist
          (locatedCauchyModulusSelectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyModulusSelectorFields :
    LocatedCauchyModulusSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyModulusSelectorUp.mk domain window rational modulus located evidence
      history classifier provenance localName =>
      [domain, window, rational, modulus, located, evidence, history, classifier,
        provenance, localName]

def locatedCauchyModulusSelectorToEventFlow :
    LocatedCauchyModulusSelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (locatedCauchyModulusSelectorFields x).map locatedCauchyModulusSelectorEncodeBHist

private def locatedCauchyModulusSelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      locatedCauchyModulusSelectorEventAtDefault index rest

def locatedCauchyModulusSelectorFromEventFlow
    (ef : EventFlow) : Option LocatedCauchyModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyModulusSelectorUp.mk
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 0 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 1 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 2 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 3 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 4 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 5 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 6 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 7 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 8 ef))
      (locatedCauchyModulusSelectorDecodeBHist
        (locatedCauchyModulusSelectorEventAtDefault 9 ef)))

private theorem LocatedCauchyModulusSelectorUp_round_trip
    (x : LocatedCauchyModulusSelectorUp) :
    locatedCauchyModulusSelectorFromEventFlow
        (locatedCauchyModulusSelectorToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk domain window rational modulus located evidence history classifier provenance
      localName =>
      change
        some
          (LocatedCauchyModulusSelectorUp.mk
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist domain))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist window))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist rational))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist modulus))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist located))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist evidence))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist history))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist classifier))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist provenance))
            (locatedCauchyModulusSelectorDecodeBHist
              (locatedCauchyModulusSelectorEncodeBHist localName))) =
          some
            (LocatedCauchyModulusSelectorUp.mk domain window rational modulus located
              evidence history classifier provenance localName)
      rw [LocatedCauchyModulusSelectorUp_decode domain,
        LocatedCauchyModulusSelectorUp_decode window,
        LocatedCauchyModulusSelectorUp_decode rational,
        LocatedCauchyModulusSelectorUp_decode modulus,
        LocatedCauchyModulusSelectorUp_decode located,
        LocatedCauchyModulusSelectorUp_decode evidence,
        LocatedCauchyModulusSelectorUp_decode history,
        LocatedCauchyModulusSelectorUp_decode classifier,
        LocatedCauchyModulusSelectorUp_decode provenance,
        LocatedCauchyModulusSelectorUp_decode localName]

private theorem LocatedCauchyModulusSelectorUp_toEventFlow_injective
    {x y : LocatedCauchyModulusSelectorUp} :
    locatedCauchyModulusSelectorToEventFlow x =
        locatedCauchyModulusSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyModulusSelectorFromEventFlow
          (locatedCauchyModulusSelectorToEventFlow x) =
        locatedCauchyModulusSelectorFromEventFlow
          (locatedCauchyModulusSelectorToEventFlow y) :=
    congrArg locatedCauchyModulusSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchyModulusSelectorUp_round_trip x).symm
      (Eq.trans hread (LocatedCauchyModulusSelectorUp_round_trip y)))

private theorem LocatedCauchyModulusSelectorUp_fields :
    ∀ x y : LocatedCauchyModulusSelectorUp,
      locatedCauchyModulusSelectorFields x =
          locatedCauchyModulusSelectorFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk d1 w1 q1 m1 l1 e1 h1 c1 p1 n1 =>
      cases y with
      | mk d2 w2 q2 m2 l2 e2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance locatedCauchyModulusSelectorBHistCarrier :
    BHistCarrier LocatedCauchyModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyModulusSelectorToEventFlow
  fromEventFlow := locatedCauchyModulusSelectorFromEventFlow

instance locatedCauchyModulusSelectorChapterTasteGate :
    ChapterTasteGate LocatedCauchyModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyModulusSelectorFromEventFlow
          (locatedCauchyModulusSelectorToEventFlow x) =
        some x
    exact LocatedCauchyModulusSelectorUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyModulusSelectorUp_toEventFlow_injective heq)

instance locatedCauchyModulusSelectorFieldFaithful :
    FieldFaithful LocatedCauchyModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCauchyModulusSelectorFields
  field_faithful := LocatedCauchyModulusSelectorUp_fields

def taste_gate : ChapterTasteGate LocatedCauchyModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCauchyModulusSelectorChapterTasteGate

theorem LocatedCauchyModulusSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchyModulusSelectorDecodeBHist
          (locatedCauchyModulusSelectorEncodeBHist h) =
        h) ∧
      (∀ x : LocatedCauchyModulusSelectorUp,
        locatedCauchyModulusSelectorFromEventFlow
            (locatedCauchyModulusSelectorToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedCauchyModulusSelectorUp,
          locatedCauchyModulusSelectorToEventFlow x =
              locatedCauchyModulusSelectorToEventFlow y →
            x = y) ∧
          locatedCauchyModulusSelectorEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedCauchyModulusSelectorUp_decode,
      LocatedCauchyModulusSelectorUp_round_trip,
      fun x y heq => LocatedCauchyModulusSelectorUp_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedCauchyModulusSelectorUp
