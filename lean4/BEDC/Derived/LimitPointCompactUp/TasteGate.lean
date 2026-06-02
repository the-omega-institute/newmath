import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitPointCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitPointCompactUp : Type where
  | mk (K S B W Q E H C P N : BHist) : LimitPointCompactUp
  deriving DecidableEq

def limitPointCompactEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitPointCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitPointCompactEncodeBHist h

def limitPointCompactDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitPointCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitPointCompactDecodeBHist tail)

private theorem LimitPointCompactTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, limitPointCompactDecodeBHist (limitPointCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limitPointCompactFields : LimitPointCompactUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitPointCompactUp.mk K S B W Q E H C P N => [K, S, B, W, Q, E, H, C, P, N]

def limitPointCompactToEventFlow : LimitPointCompactUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (limitPointCompactFields x).map limitPointCompactEncodeBHist

private def limitPointCompactEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => limitPointCompactEventAtDefault index rest

def limitPointCompactFromEventFlow (ef : EventFlow) : Option LimitPointCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LimitPointCompactUp.mk
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 0 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 1 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 2 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 3 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 4 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 5 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 6 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 7 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 8 ef))
      (limitPointCompactDecodeBHist (limitPointCompactEventAtDefault 9 ef)))

private theorem LimitPointCompactTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LimitPointCompactUp,
      limitPointCompactFromEventFlow (limitPointCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K S B W Q E H C P N =>
      change
        some
          (LimitPointCompactUp.mk
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist K))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist S))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist B))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist W))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist Q))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist E))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist H))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist C))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist P))
            (limitPointCompactDecodeBHist (limitPointCompactEncodeBHist N))) =
          some (LimitPointCompactUp.mk K S B W Q E H C P N)
      rw [LimitPointCompactTasteGate_single_carrier_alignment_decode K,
        LimitPointCompactTasteGate_single_carrier_alignment_decode S,
        LimitPointCompactTasteGate_single_carrier_alignment_decode B,
        LimitPointCompactTasteGate_single_carrier_alignment_decode W,
        LimitPointCompactTasteGate_single_carrier_alignment_decode Q,
        LimitPointCompactTasteGate_single_carrier_alignment_decode E,
        LimitPointCompactTasteGate_single_carrier_alignment_decode H,
        LimitPointCompactTasteGate_single_carrier_alignment_decode C,
        LimitPointCompactTasteGate_single_carrier_alignment_decode P,
        LimitPointCompactTasteGate_single_carrier_alignment_decode N]

private theorem LimitPointCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LimitPointCompactUp} :
    limitPointCompactToEventFlow x = limitPointCompactToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = limitPointCompactFromEventFlow (limitPointCompactToEventFlow x) :=
        (LimitPointCompactTasteGate_single_carrier_alignment_round_trip x).symm
      _ = limitPointCompactFromEventFlow (limitPointCompactToEventFlow y) :=
        congrArg limitPointCompactFromEventFlow hxy
      _ = some y := LimitPointCompactTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem LimitPointCompactTasteGate_single_carrier_alignment_fields :
    ∀ x y : LimitPointCompactUp, limitPointCompactFields x = limitPointCompactFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 S1 B1 W1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 S2 B2 W2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance limitPointCompactBHistCarrier : BHistCarrier LimitPointCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitPointCompactToEventFlow
  fromEventFlow := limitPointCompactFromEventFlow

instance limitPointCompactChapterTasteGate : ChapterTasteGate LimitPointCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitPointCompactFromEventFlow (limitPointCompactToEventFlow x) = some x
    exact LimitPointCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LimitPointCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance limitPointCompactFieldFaithful : FieldFaithful LimitPointCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := limitPointCompactFields
  field_faithful := LimitPointCompactTasteGate_single_carrier_alignment_fields

instance limitPointCompactNontrivial : Nontrivial LimitPointCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LimitPointCompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LimitPointCompactUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LimitPointCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  limitPointCompactChapterTasteGate

theorem LimitPointCompactTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LimitPointCompactUp) ∧
      Nonempty (FieldFaithful LimitPointCompactUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LimitPointCompactUp) ∧
          (∀ h : BHist,
            limitPointCompactDecodeBHist (limitPointCompactEncodeBHist h) = h) ∧
            (∀ x : LimitPointCompactUp,
              limitPointCompactFromEventFlow (limitPointCompactToEventFlow x) = some x) ∧
              (∀ x y : LimitPointCompactUp,
                limitPointCompactToEventFlow x = limitPointCompactToEventFlow y -> x = y) ∧
                limitPointCompactEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨limitPointCompactChapterTasteGate⟩,
      ⟨limitPointCompactFieldFaithful⟩,
      ⟨limitPointCompactNontrivial⟩,
      LimitPointCompactTasteGate_single_carrier_alignment_decode,
      LimitPointCompactTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LimitPointCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LimitPointCompactUp
