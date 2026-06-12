import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetDiagonalUp : Type where
  | mk (A M K T S Q R H C P N : BHist) : CauchyNetDiagonalUp
  deriving DecidableEq

def cauchyNetDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetDiagonalEncodeBHist h

def cauchyNetDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetDiagonalDecodeBHist tail)

private theorem CauchyNetDiagonalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNetDiagonalFields : CauchyNetDiagonalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetDiagonalUp.mk A M K T S Q R H C P N => [A, M, K, T, S, Q, R, H, C, P, N]

def cauchyNetDiagonalToEventFlow : CauchyNetDiagonalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyNetDiagonalFields x).map cauchyNetDiagonalEncodeBHist

private def cauchyNetDiagonalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyNetDiagonalEventAtDefault index rest

def cauchyNetDiagonalFromEventFlow (ef : EventFlow) : Option CauchyNetDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyNetDiagonalUp.mk
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 0 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 1 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 2 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 3 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 4 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 5 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 6 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 7 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 8 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 9 ef))
      (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEventAtDefault 10 ef)))

private theorem CauchyNetDiagonalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyNetDiagonalUp,
      cauchyNetDiagonalFromEventFlow (cauchyNetDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M K T S Q R H C P N =>
      change
        some
          (CauchyNetDiagonalUp.mk
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist A))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist M))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist K))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist T))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist S))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist Q))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist R))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist H))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist C))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist P))
            (cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist N))) =
          some (CauchyNetDiagonalUp.mk A M K T S Q R H C P N)
      rw [CauchyNetDiagonalTasteGate_single_carrier_alignment_decode A,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode M,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode K,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode T,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode S,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode Q,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode R,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode H,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode C,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode P,
        CauchyNetDiagonalTasteGate_single_carrier_alignment_decode N]

private theorem CauchyNetDiagonalTasteGate_single_carrier_alignment_injective
    {x y : CauchyNetDiagonalUp} :
    cauchyNetDiagonalToEventFlow x = cauchyNetDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetDiagonalFromEventFlow (cauchyNetDiagonalToEventFlow x) =
        cauchyNetDiagonalFromEventFlow (cauchyNetDiagonalToEventFlow y) :=
    congrArg cauchyNetDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyNetDiagonalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyNetDiagonalTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyNetDiagonalTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyNetDiagonalUp,
      cauchyNetDiagonalFields x = cauchyNetDiagonalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 M1 K1 T1 S1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 M2 K2 T2 S2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyNetDiagonalBHistCarrier : BHistCarrier CauchyNetDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetDiagonalToEventFlow
  fromEventFlow := cauchyNetDiagonalFromEventFlow

instance cauchyNetDiagonalChapterTasteGate : ChapterTasteGate CauchyNetDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyNetDiagonalFromEventFlow (cauchyNetDiagonalToEventFlow x) = some x
    exact CauchyNetDiagonalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyNetDiagonalTasteGate_single_carrier_alignment_injective heq)

instance cauchyNetDiagonalFieldFaithful : FieldFaithful CauchyNetDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNetDiagonalFields
  field_faithful := CauchyNetDiagonalTasteGate_single_carrier_alignment_fields

instance cauchyNetDiagonalNontrivial : Nontrivial CauchyNetDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNetDiagonalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyNetDiagonalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyNetDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetDiagonalChapterTasteGate

theorem CauchyNetDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyNetDiagonalDecodeBHist (cauchyNetDiagonalEncodeBHist h) = h) ∧
      (∀ x : CauchyNetDiagonalUp,
        cauchyNetDiagonalFromEventFlow (cauchyNetDiagonalToEventFlow x) = some x) ∧
        (∀ x y : CauchyNetDiagonalUp,
          cauchyNetDiagonalToEventFlow x = cauchyNetDiagonalToEventFlow y →
            x = y) ∧
          cauchyNetDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyNetDiagonalTasteGate_single_carrier_alignment_decode,
      CauchyNetDiagonalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyNetDiagonalTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyNetDiagonalUp
