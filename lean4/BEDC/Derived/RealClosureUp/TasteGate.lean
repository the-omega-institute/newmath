import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealClosureUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealClosureUp : Type where
  | mk (X T S Q A E H C P N : BHist) : RealClosureUp
  deriving DecidableEq

def realClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realClosureEncodeBHist h

def realClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realClosureDecodeBHist tail)

private theorem RealClosureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realClosureDecodeBHist (realClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realClosureFields : RealClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealClosureUp.mk X T S Q A E H C P N => [X, T, S, Q, A, E, H, C, P, N]

def realClosureToEventFlow : RealClosureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realClosureFields x).map realClosureEncodeBHist

private def realClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realClosureEventAtDefault index rest

def realClosureFromEventFlow (ef : EventFlow) : Option RealClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealClosureUp.mk
      (realClosureDecodeBHist (realClosureEventAtDefault 0 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 1 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 2 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 3 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 4 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 5 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 6 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 7 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 8 ef))
      (realClosureDecodeBHist (realClosureEventAtDefault 9 ef)))

private theorem RealClosureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealClosureUp, realClosureFromEventFlow (realClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X T S Q A E H C P N =>
      change
        some
          (RealClosureUp.mk
            (realClosureDecodeBHist (realClosureEncodeBHist X))
            (realClosureDecodeBHist (realClosureEncodeBHist T))
            (realClosureDecodeBHist (realClosureEncodeBHist S))
            (realClosureDecodeBHist (realClosureEncodeBHist Q))
            (realClosureDecodeBHist (realClosureEncodeBHist A))
            (realClosureDecodeBHist (realClosureEncodeBHist E))
            (realClosureDecodeBHist (realClosureEncodeBHist H))
            (realClosureDecodeBHist (realClosureEncodeBHist C))
            (realClosureDecodeBHist (realClosureEncodeBHist P))
            (realClosureDecodeBHist (realClosureEncodeBHist N))) =
          some (RealClosureUp.mk X T S Q A E H C P N)
      rw [RealClosureTasteGate_single_carrier_alignment_decode X,
        RealClosureTasteGate_single_carrier_alignment_decode T,
        RealClosureTasteGate_single_carrier_alignment_decode S,
        RealClosureTasteGate_single_carrier_alignment_decode Q,
        RealClosureTasteGate_single_carrier_alignment_decode A,
        RealClosureTasteGate_single_carrier_alignment_decode E,
        RealClosureTasteGate_single_carrier_alignment_decode H,
        RealClosureTasteGate_single_carrier_alignment_decode C,
        RealClosureTasteGate_single_carrier_alignment_decode P,
        RealClosureTasteGate_single_carrier_alignment_decode N]

private theorem RealClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealClosureUp} :
    realClosureToEventFlow x = realClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realClosureFromEventFlow (realClosureToEventFlow x) =
        realClosureFromEventFlow (realClosureToEventFlow y) :=
    congrArg realClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealClosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealClosureTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealClosureUp, realClosureFields x = realClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 T1 S1 Q1 A1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 T2 S2 Q2 A2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realClosureBHistCarrier : BHistCarrier RealClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realClosureToEventFlow
  fromEventFlow := realClosureFromEventFlow

instance realClosureChapterTasteGate : ChapterTasteGate RealClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realClosureFromEventFlow (realClosureToEventFlow x) = some x
    exact RealClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realClosureFieldFaithful : FieldFaithful RealClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realClosureFields
  field_faithful := RealClosureTasteGate_single_carrier_alignment_fields

instance realClosureNontrivial : Nontrivial RealClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def realClosureTasteGate : ChapterTasteGate RealClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realClosureChapterTasteGate

theorem RealClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, realClosureDecodeBHist (realClosureEncodeBHist h) = h) ∧
      (∀ x : RealClosureUp, realClosureFromEventFlow (realClosureToEventFlow x) = some x) ∧
        (∀ x y : RealClosureUp, realClosureToEventFlow x = realClosureToEventFlow y → x = y) ∧
          realClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨RealClosureTasteGate_single_carrier_alignment_decode,
      RealClosureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealClosureUp.TasteGate
