import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorFunctionUp : Type where
  | mk (S T B G E H C P N : BHist) : CantorFunctionUp
  deriving DecidableEq

def cantorFunctionEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorFunctionEncodeBHist h

def cantorFunctionDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorFunctionDecodeBHist tail)

private theorem cantorFunction_decode_encode :
    ∀ h : BHist, cantorFunctionDecodeBHist (cantorFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorFunctionFields : CantorFunctionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CantorFunctionUp.mk S T B G E H C P N => [S, T, B, G, E, H, C, P, N]

def cantorFunctionToEventFlow : CantorFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CantorFunctionUp.mk S T B G E H C P N =>
      [cantorFunctionEncodeBHist S,
        cantorFunctionEncodeBHist T,
        cantorFunctionEncodeBHist B,
        cantorFunctionEncodeBHist G,
        cantorFunctionEncodeBHist E,
        cantorFunctionEncodeBHist H,
        cantorFunctionEncodeBHist C,
        cantorFunctionEncodeBHist P,
        cantorFunctionEncodeBHist N]

private def cantorFunctionEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorFunctionEventAt index rest

def cantorFunctionFromEventFlow : EventFlow → Option CantorFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CantorFunctionUp.mk
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 0 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 1 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 2 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 3 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 4 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 5 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 6 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 7 ef))
        (cantorFunctionDecodeBHist (cantorFunctionEventAt 8 ef)))

private theorem cantorFunction_round_trip :
    ∀ x : CantorFunctionUp,
      cantorFunctionFromEventFlow (cantorFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T B G E H C P N =>
      change
        some
          (CantorFunctionUp.mk
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist S))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist T))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist B))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist G))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist E))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist H))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist C))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist P))
            (cantorFunctionDecodeBHist (cantorFunctionEncodeBHist N))) =
          some (CantorFunctionUp.mk S T B G E H C P N)
      rw [cantorFunction_decode_encode S,
        cantorFunction_decode_encode T,
        cantorFunction_decode_encode B,
        cantorFunction_decode_encode G,
        cantorFunction_decode_encode E,
        cantorFunction_decode_encode H,
        cantorFunction_decode_encode C,
        cantorFunction_decode_encode P,
        cantorFunction_decode_encode N]

private theorem cantorFunctionToEventFlow_injective {x y : CantorFunctionUp} :
    cantorFunctionToEventFlow x = cantorFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = cantorFunctionFromEventFlow (cantorFunctionToEventFlow x) :=
        (cantorFunction_round_trip x).symm
      _ = cantorFunctionFromEventFlow (cantorFunctionToEventFlow y) :=
        congrArg cantorFunctionFromEventFlow hxy
      _ = some y := cantorFunction_round_trip y
  exact Option.some.inj hsome

private theorem cantorFunction_field_faithful :
    ∀ x y : CantorFunctionUp, cantorFunctionFields x = cantorFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 B1 G1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 B2 G2 E2 H2 C2 P2 N2 =>
          injection hfields with hS tail0
          injection tail0 with hT tail1
          injection tail1 with hB tail2
          injection tail2 with hG tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hS
          subst hT
          subst hB
          subst hG
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cantorFunctionBHistCarrier : BHistCarrier CantorFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorFunctionToEventFlow
  fromEventFlow := cantorFunctionFromEventFlow

instance cantorFunctionChapterTasteGate : ChapterTasteGate CantorFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorFunctionFromEventFlow (cantorFunctionToEventFlow x) = some x
    exact cantorFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorFunctionToEventFlow_injective heq)

instance cantorFunctionFieldFaithful : FieldFaithful CantorFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorFunctionFields
  field_faithful := cantorFunction_field_faithful

instance cantorFunctionNontrivial : Nontrivial CantorFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CantorFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorFunctionChapterTasteGate

theorem CantorFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cantorFunctionDecodeBHist (cantorFunctionEncodeBHist h) = h) ∧
      (∀ x : CantorFunctionUp,
        cantorFunctionFromEventFlow (cantorFunctionToEventFlow x) = some x) ∧
        (∀ x y : CantorFunctionUp,
          cantorFunctionToEventFlow x = cantorFunctionToEventFlow y → x = y) ∧
          cantorFunctionEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CantorFunctionUp, cantorFunctionFields x = cantorFunctionFields y → x = y) ∧
              (∃ x y : CantorFunctionUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cantorFunction_decode_encode
  · constructor
    · exact cantorFunction_round_trip
    · constructor
      · intro x y heq
        exact cantorFunctionToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact cantorFunction_field_faithful
          · exact
              ⟨CantorFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                CantorFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.CantorFunctionUp
