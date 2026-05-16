import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicToleranceTriangleLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicToleranceTriangleLedgerUp : Type where
  | mk (Dm Dn Im In Em En M Q T H C P N : BHist) : DyadicToleranceTriangleLedgerUp
  deriving DecidableEq

def dyadicToleranceTriangleLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicToleranceTriangleLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicToleranceTriangleLedgerEncodeBHist h

def dyadicToleranceTriangleLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicToleranceTriangleLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicToleranceTriangleLedgerDecodeBHist tail)

private theorem dyadicToleranceTriangleLedger_decode_encode_bhist :
    ∀ h : BHist,
      dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicToleranceTriangleLedgerToEventFlow :
    DyadicToleranceTriangleLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicToleranceTriangleLedgerUp.mk Dm Dn Im In Em En M Q T H C P N =>
      [dyadicToleranceTriangleLedgerEncodeBHist Dm,
        dyadicToleranceTriangleLedgerEncodeBHist Dn,
        dyadicToleranceTriangleLedgerEncodeBHist Im,
        dyadicToleranceTriangleLedgerEncodeBHist In,
        dyadicToleranceTriangleLedgerEncodeBHist Em,
        dyadicToleranceTriangleLedgerEncodeBHist En,
        dyadicToleranceTriangleLedgerEncodeBHist M,
        dyadicToleranceTriangleLedgerEncodeBHist Q,
        dyadicToleranceTriangleLedgerEncodeBHist T,
        dyadicToleranceTriangleLedgerEncodeBHist H,
        dyadicToleranceTriangleLedgerEncodeBHist C,
        dyadicToleranceTriangleLedgerEncodeBHist P,
        dyadicToleranceTriangleLedgerEncodeBHist N]

private def dyadicToleranceTriangleLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicToleranceTriangleLedgerEventAtDefault index rest

def dyadicToleranceTriangleLedgerFromEventFlow (ef : EventFlow) :
    Option DyadicToleranceTriangleLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicToleranceTriangleLedgerUp.mk
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 0 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 1 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 2 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 3 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 4 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 5 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 6 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 7 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 8 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 9 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 10 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 11 ef))
      (dyadicToleranceTriangleLedgerDecodeBHist
        (dyadicToleranceTriangleLedgerEventAtDefault 12 ef)))

private theorem dyadicToleranceTriangleLedger_round_trip :
    ∀ x : DyadicToleranceTriangleLedgerUp,
      dyadicToleranceTriangleLedgerFromEventFlow
        (dyadicToleranceTriangleLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Dm Dn Im In Em En M Q T H C P N =>
      change
        some
          (DyadicToleranceTriangleLedgerUp.mk
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist Dm))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist Dn))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist Im))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist In))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist Em))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist En))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist M))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist Q))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist T))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist H))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist C))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist P))
            (dyadicToleranceTriangleLedgerDecodeBHist
              (dyadicToleranceTriangleLedgerEncodeBHist N))) =
          some (DyadicToleranceTriangleLedgerUp.mk Dm Dn Im In Em En M Q T H C P N)
      rw [dyadicToleranceTriangleLedger_decode_encode_bhist Dm,
        dyadicToleranceTriangleLedger_decode_encode_bhist Dn,
        dyadicToleranceTriangleLedger_decode_encode_bhist Im,
        dyadicToleranceTriangleLedger_decode_encode_bhist In,
        dyadicToleranceTriangleLedger_decode_encode_bhist Em,
        dyadicToleranceTriangleLedger_decode_encode_bhist En,
        dyadicToleranceTriangleLedger_decode_encode_bhist M,
        dyadicToleranceTriangleLedger_decode_encode_bhist Q,
        dyadicToleranceTriangleLedger_decode_encode_bhist T,
        dyadicToleranceTriangleLedger_decode_encode_bhist H,
        dyadicToleranceTriangleLedger_decode_encode_bhist C,
        dyadicToleranceTriangleLedger_decode_encode_bhist P,
        dyadicToleranceTriangleLedger_decode_encode_bhist N]

private theorem dyadicToleranceTriangleLedgerToEventFlow_injective
    {x y : DyadicToleranceTriangleLedgerUp} :
    dyadicToleranceTriangleLedgerToEventFlow x = dyadicToleranceTriangleLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicToleranceTriangleLedgerFromEventFlow
          (dyadicToleranceTriangleLedgerToEventFlow x) =
        dyadicToleranceTriangleLedgerFromEventFlow
          (dyadicToleranceTriangleLedgerToEventFlow y) :=
    congrArg dyadicToleranceTriangleLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicToleranceTriangleLedger_round_trip x).symm
      (Eq.trans hread (dyadicToleranceTriangleLedger_round_trip y)))

private def dyadicToleranceTriangleLedgerFields :
    DyadicToleranceTriangleLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicToleranceTriangleLedgerUp.mk Dm Dn Im In Em En M Q T H C P N =>
      [Dm, Dn, Im, In, Em, En, M, Q, T, H, C, P, N]

private theorem dyadicToleranceTriangleLedger_field_faithful :
    ∀ x y : DyadicToleranceTriangleLedgerUp,
      dyadicToleranceTriangleLedgerFields x = dyadicToleranceTriangleLedgerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Dm₁ Dn₁ Im₁ In₁ Em₁ En₁ M₁ Q₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Dm₂ Dn₂ Im₂ In₂ Em₂ En₂ M₂ Q₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicToleranceTriangleLedgerBHistCarrier :
    BHistCarrier DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicToleranceTriangleLedgerToEventFlow
  fromEventFlow := dyadicToleranceTriangleLedgerFromEventFlow

instance dyadicToleranceTriangleLedgerChapterTasteGate :
    ChapterTasteGate DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicToleranceTriangleLedgerFromEventFlow
      (dyadicToleranceTriangleLedgerToEventFlow x) = some x
    exact dyadicToleranceTriangleLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicToleranceTriangleLedgerToEventFlow_injective heq)

instance dyadicToleranceTriangleLedgerFieldFaithful :
    FieldFaithful DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicToleranceTriangleLedgerFields
  field_faithful := dyadicToleranceTriangleLedger_field_faithful

instance dyadicToleranceTriangleLedgerNontrivial : Nontrivial DyadicToleranceTriangleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicToleranceTriangleLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DyadicToleranceTriangleLedgerUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicToleranceTriangleLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicToleranceTriangleLedgerChapterTasteGate

theorem DyadicToleranceTriangleLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        dyadicToleranceTriangleLedgerDecodeBHist
          (dyadicToleranceTriangleLedgerEncodeBHist h) = h) ∧
      (∀ x : DyadicToleranceTriangleLedgerUp,
        dyadicToleranceTriangleLedgerFromEventFlow
          (dyadicToleranceTriangleLedgerToEventFlow x) = some x) ∧
        (∀ x y : DyadicToleranceTriangleLedgerUp,
          dyadicToleranceTriangleLedgerToEventFlow x =
            dyadicToleranceTriangleLedgerToEventFlow y → x = y) ∧
          dyadicToleranceTriangleLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk Dm Dn Im In Em En M Q T H C P N =>
          change
            some
              (DyadicToleranceTriangleLedgerUp.mk
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist Dm))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist Dn))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist Im))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist In))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist Em))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist En))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist M))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist Q))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist T))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist H))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist C))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist P))
                (dyadicToleranceTriangleLedgerDecodeBHist
                  (dyadicToleranceTriangleLedgerEncodeBHist N))) =
              some (DyadicToleranceTriangleLedgerUp.mk Dm Dn Im In Em En M Q T H C P N)
          rw [dyadicToleranceTriangleLedger_decode_encode_bhist Dm,
            dyadicToleranceTriangleLedger_decode_encode_bhist Dn,
            dyadicToleranceTriangleLedger_decode_encode_bhist Im,
            dyadicToleranceTriangleLedger_decode_encode_bhist In,
            dyadicToleranceTriangleLedger_decode_encode_bhist Em,
            dyadicToleranceTriangleLedger_decode_encode_bhist En,
            dyadicToleranceTriangleLedger_decode_encode_bhist M,
            dyadicToleranceTriangleLedger_decode_encode_bhist Q,
            dyadicToleranceTriangleLedger_decode_encode_bhist T,
            dyadicToleranceTriangleLedger_decode_encode_bhist H,
            dyadicToleranceTriangleLedger_decode_encode_bhist C,
            dyadicToleranceTriangleLedger_decode_encode_bhist P,
            dyadicToleranceTriangleLedger_decode_encode_bhist N]
    · constructor
      · intro x y heq
        have hread :
            dyadicToleranceTriangleLedgerFromEventFlow
                (dyadicToleranceTriangleLedgerToEventFlow x) =
              dyadicToleranceTriangleLedgerFromEventFlow
                (dyadicToleranceTriangleLedgerToEventFlow y) :=
          congrArg dyadicToleranceTriangleLedgerFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (dyadicToleranceTriangleLedger_round_trip x).symm
            (Eq.trans hread (dyadicToleranceTriangleLedger_round_trip y)))
      · rfl

end BEDC.Derived.DyadicToleranceTriangleLedgerUp.TasteGate
