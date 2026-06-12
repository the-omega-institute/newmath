import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceDiamondLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceDiamondLedgerUp : Type where
  | mk (T R J B O X H C P N : BHist) : MetaCICConfluenceDiamondLedgerUp
  deriving DecidableEq

def metaCICConfluenceDiamondLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceDiamondLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceDiamondLedgerEncodeBHist h

def metaCICConfluenceDiamondLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceDiamondLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceDiamondLedgerDecodeBHist tail)

private theorem metaCICConfluenceDiamondLedgerDecodeEncodeBHist :
    ∀ h : BHist,
      metaCICConfluenceDiamondLedgerDecodeBHist
          (metaCICConfluenceDiamondLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICConfluenceDiamondLedgerFields :
    MetaCICConfluenceDiamondLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceDiamondLedgerUp.mk T R J B O X H C P N =>
      [T, R, J, B, O, X, H, C, P, N]

def metaCICConfluenceDiamondLedgerToEventFlow :
    MetaCICConfluenceDiamondLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICConfluenceDiamondLedgerFields x).map
      metaCICConfluenceDiamondLedgerEncodeBHist

private def metaCICConfluenceDiamondLedgerEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICConfluenceDiamondLedgerEventAtDefault index rest

def metaCICConfluenceDiamondLedgerFromEventFlow
    (ef : EventFlow) : Option MetaCICConfluenceDiamondLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICConfluenceDiamondLedgerUp.mk
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 0 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 1 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 2 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 3 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 4 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 5 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 6 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 7 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 8 ef))
      (metaCICConfluenceDiamondLedgerDecodeBHist
        (metaCICConfluenceDiamondLedgerEventAtDefault 9 ef)))

private theorem metaCICConfluenceDiamondLedger_round_trip :
    ∀ x : MetaCICConfluenceDiamondLedgerUp,
      metaCICConfluenceDiamondLedgerFromEventFlow
          (metaCICConfluenceDiamondLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T R J B O X H C P N =>
      change
        some
            (MetaCICConfluenceDiamondLedgerUp.mk
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist T))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist R))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist J))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist B))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist O))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist X))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist H))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist C))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist P))
              (metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist N))) =
          some (MetaCICConfluenceDiamondLedgerUp.mk T R J B O X H C P N)
      rw [metaCICConfluenceDiamondLedgerDecodeEncodeBHist T,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist R,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist J,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist B,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist O,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist X,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist H,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist C,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist P,
        metaCICConfluenceDiamondLedgerDecodeEncodeBHist N]

private theorem metaCICConfluenceDiamondLedgerToEventFlow_injective
    {x y : MetaCICConfluenceDiamondLedgerUp} :
    metaCICConfluenceDiamondLedgerToEventFlow x =
      metaCICConfluenceDiamondLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceDiamondLedgerFromEventFlow
          (metaCICConfluenceDiamondLedgerToEventFlow x) =
        metaCICConfluenceDiamondLedgerFromEventFlow
          (metaCICConfluenceDiamondLedgerToEventFlow y) :=
    congrArg metaCICConfluenceDiamondLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (metaCICConfluenceDiamondLedger_round_trip x).symm
      (Eq.trans hread (metaCICConfluenceDiamondLedger_round_trip y)))

private theorem metaCICConfluenceDiamondLedgerFields_faithful :
    ∀ x y : MetaCICConfluenceDiamondLedgerUp,
      metaCICConfluenceDiamondLedgerFields x =
        metaCICConfluenceDiamondLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 R1 J1 B1 O1 X1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 R2 J2 B2 O2 X2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metaCICConfluenceDiamondLedgerBHistCarrier :
    BHistCarrier MetaCICConfluenceDiamondLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceDiamondLedgerToEventFlow
  fromEventFlow := metaCICConfluenceDiamondLedgerFromEventFlow

instance metaCICConfluenceDiamondLedgerChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceDiamondLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConfluenceDiamondLedgerFromEventFlow
        (metaCICConfluenceDiamondLedgerToEventFlow x) = some x
    exact metaCICConfluenceDiamondLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConfluenceDiamondLedgerToEventFlow_injective heq)

instance metaCICConfluenceDiamondLedgerFieldFaithful :
    FieldFaithful MetaCICConfluenceDiamondLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICConfluenceDiamondLedgerFields
  field_faithful := metaCICConfluenceDiamondLedgerFields_faithful

instance metaCICConfluenceDiamondLedgerNontrivial :
    Nontrivial MetaCICConfluenceDiamondLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICConfluenceDiamondLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICConfluenceDiamondLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICConfluenceDiamondLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceDiamondLedgerChapterTasteGate

theorem MetaCICConfluenceDiamondLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetaCICConfluenceDiamondLedgerUp) ∧
      Nonempty (FieldFaithful MetaCICConfluenceDiamondLedgerUp) ∧
        Nonempty (Nontrivial MetaCICConfluenceDiamondLedgerUp) ∧
          (∀ h : BHist,
            metaCICConfluenceDiamondLedgerDecodeBHist
                (metaCICConfluenceDiamondLedgerEncodeBHist h) =
              h) ∧
            (∀ x : MetaCICConfluenceDiamondLedgerUp,
              metaCICConfluenceDiamondLedgerFromEventFlow
                  (metaCICConfluenceDiamondLedgerToEventFlow x) =
                some x) ∧
              (∀ x y : MetaCICConfluenceDiamondLedgerUp,
                metaCICConfluenceDiamondLedgerToEventFlow x =
                    metaCICConfluenceDiamondLedgerToEventFlow y →
                  x = y) ∧
                metaCICConfluenceDiamondLedgerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro metaCICConfluenceDiamondLedgerChapterTasteGate,
      Nonempty.intro metaCICConfluenceDiamondLedgerFieldFaithful,
      Nonempty.intro metaCICConfluenceDiamondLedgerNontrivial,
      metaCICConfluenceDiamondLedgerDecodeEncodeBHist,
      metaCICConfluenceDiamondLedger_round_trip,
      (fun _ _ heq => metaCICConfluenceDiamondLedgerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICConfluenceDiamondLedgerUp
