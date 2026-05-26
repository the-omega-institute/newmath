import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RolleTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RolleTheoremUp : Type where
  | mk (A B E F Q D I Z H C P N : BHist) : RolleTheoremUp
  deriving DecidableEq

def rolleTheoremEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rolleTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rolleTheoremEncodeBHist h

def rolleTheoremDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rolleTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rolleTheoremDecodeBHist tail)

private theorem rolleTheoremDecode_encode :
    ∀ h : BHist, rolleTheoremDecodeBHist (rolleTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rolleTheoremToEventFlow : RolleTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RolleTheoremUp.mk A B E F Q D I Z H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        rolleTheoremEncodeBHist A,
        rolleTheoremEncodeBHist B,
        rolleTheoremEncodeBHist E,
        rolleTheoremEncodeBHist F,
        rolleTheoremEncodeBHist Q,
        rolleTheoremEncodeBHist D,
        rolleTheoremEncodeBHist I,
        rolleTheoremEncodeBHist Z,
        rolleTheoremEncodeBHist H,
        rolleTheoremEncodeBHist C,
        rolleTheoremEncodeBHist P,
        rolleTheoremEncodeBHist N]

private def rolleTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rolleTheoremEventAtDefault index rest

def rolleTheoremFromEventFlow : EventFlow → Option RolleTheoremUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RolleTheoremUp.mk
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 1 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 2 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 3 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 4 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 5 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 6 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 7 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 8 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 9 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 10 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 11 ef))
      (rolleTheoremDecodeBHist (rolleTheoremEventAtDefault 12 ef)))

private theorem rolleTheorem_round_trip :
    ∀ x : RolleTheoremUp,
      rolleTheoremFromEventFlow (rolleTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B E F Q D I Z H C P N =>
      change
        some
          (RolleTheoremUp.mk
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist A))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist B))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist E))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist F))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist Q))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist D))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist I))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist Z))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist H))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist C))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist P))
            (rolleTheoremDecodeBHist (rolleTheoremEncodeBHist N))) =
          some (RolleTheoremUp.mk A B E F Q D I Z H C P N)
      rw [rolleTheoremDecode_encode A, rolleTheoremDecode_encode B,
        rolleTheoremDecode_encode E, rolleTheoremDecode_encode F,
        rolleTheoremDecode_encode Q, rolleTheoremDecode_encode D,
        rolleTheoremDecode_encode I, rolleTheoremDecode_encode Z,
        rolleTheoremDecode_encode H, rolleTheoremDecode_encode C,
        rolleTheoremDecode_encode P, rolleTheoremDecode_encode N]

private theorem rolleTheoremToEventFlow_injective {x y : RolleTheoremUp} :
    rolleTheoremToEventFlow x = rolleTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rolleTheoremFromEventFlow (rolleTheoremToEventFlow x) =
        rolleTheoremFromEventFlow (rolleTheoremToEventFlow y) :=
    congrArg rolleTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (rolleTheorem_round_trip x).symm
      (Eq.trans hread (rolleTheorem_round_trip y)))

private def rolleTheoremFields : RolleTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RolleTheoremUp.mk A B E F Q D I Z H C P N => [A, B, E, F, Q, D, I, Z, H, C, P, N]

private theorem rolleTheorem_field_faithful :
    ∀ x y : RolleTheoremUp, rolleTheoremFields x = rolleTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 B1 E1 F1 Q1 D1 I1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 B2 E2 F2 Q2 D2 I2 Z2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance rolleTheoremBHistCarrier : BHistCarrier RolleTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rolleTheoremToEventFlow
  fromEventFlow := rolleTheoremFromEventFlow

instance rolleTheoremChapterTasteGate : ChapterTasteGate RolleTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rolleTheoremFromEventFlow (rolleTheoremToEventFlow x) = some x
    exact rolleTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rolleTheoremToEventFlow_injective heq)

instance rolleTheoremFieldFaithful : FieldFaithful RolleTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rolleTheoremFields
  field_faithful := rolleTheorem_field_faithful

def taste_gate : ChapterTasteGate RolleTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rolleTheoremChapterTasteGate

theorem RolleTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, rolleTheoremDecodeBHist (rolleTheoremEncodeBHist h) = h) ∧
      (∀ x : RolleTheoremUp,
        rolleTheoremFromEventFlow (rolleTheoremToEventFlow x) = some x) ∧
        (∀ x y : RolleTheoremUp,
          rolleTheoremToEventFlow x = rolleTheoremToEventFlow y → x = y) ∧
          rolleTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rolleTheoremDecode_encode,
      rolleTheorem_round_trip,
      (fun _ _ heq => rolleTheoremToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RolleTheoremUp
