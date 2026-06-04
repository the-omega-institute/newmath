import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductLimitUp : Type where
  | mk (X Y S Q D M A H C P N : BHist) : CauchyProductLimitUp
  deriving DecidableEq

def cauchyProductLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductLimitEncodeBHist h

def cauchyProductLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductLimitDecodeBHist tail)

private theorem cauchyProductLimitDecode_encode_bhist :
    ∀ h : BHist, cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductLimitFields : CauchyProductLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductLimitUp.mk X Y S Q D M A H C P N => [X, Y, S, Q, D, M, A, H, C, P, N]

def cauchyProductLimitToEventFlow : CauchyProductLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyProductLimitFields x).map cauchyProductLimitEncodeBHist

private def cauchyProductLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductLimitEventAtDefault index rest

def cauchyProductLimitFromEventFlow
    (ef : EventFlow) : Option CauchyProductLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductLimitUp.mk
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 0 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 1 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 2 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 3 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 4 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 5 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 6 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 7 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 8 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 9 ef))
      (cauchyProductLimitDecodeBHist (cauchyProductLimitEventAtDefault 10 ef)))

private theorem cauchyProductLimit_round_trip :
    ∀ x : CauchyProductLimitUp,
      cauchyProductLimitFromEventFlow (cauchyProductLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S Q D M A H C P N =>
      change
        some
          (CauchyProductLimitUp.mk
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist X))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist Y))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist S))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist Q))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist D))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist M))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist A))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist H))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist C))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist P))
            (cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist N))) =
          some (CauchyProductLimitUp.mk X Y S Q D M A H C P N)
      rw [cauchyProductLimitDecode_encode_bhist X, cauchyProductLimitDecode_encode_bhist Y,
        cauchyProductLimitDecode_encode_bhist S, cauchyProductLimitDecode_encode_bhist Q,
        cauchyProductLimitDecode_encode_bhist D, cauchyProductLimitDecode_encode_bhist M,
        cauchyProductLimitDecode_encode_bhist A, cauchyProductLimitDecode_encode_bhist H,
        cauchyProductLimitDecode_encode_bhist C, cauchyProductLimitDecode_encode_bhist P,
        cauchyProductLimitDecode_encode_bhist N]

private theorem cauchyProductLimitToEventFlow_injective {x y : CauchyProductLimitUp} :
    cauchyProductLimitToEventFlow x = cauchyProductLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductLimitFromEventFlow (cauchyProductLimitToEventFlow x) =
        cauchyProductLimitFromEventFlow (cauchyProductLimitToEventFlow y) :=
    congrArg cauchyProductLimitFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (cauchyProductLimit_round_trip x).symm
        (Eq.trans hread (cauchyProductLimit_round_trip y)))

instance cauchyProductLimitBHistCarrier : BHistCarrier CauchyProductLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductLimitToEventFlow
  fromEventFlow := cauchyProductLimitFromEventFlow

instance cauchyProductLimitChapterTasteGate : ChapterTasteGate CauchyProductLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductLimitFromEventFlow (cauchyProductLimitToEventFlow x) = some x
    exact cauchyProductLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductLimitToEventFlow_injective heq)

theorem CauchyProductLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyProductLimitDecodeBHist (cauchyProductLimitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyProductLimitUp) ∧
        Nonempty (ChapterTasteGate CauchyProductLimitUp) ∧
          cauchyProductLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨cauchyProductLimitDecode_encode_bhist, ⟨cauchyProductLimitBHistCarrier⟩,
      ⟨cauchyProductLimitChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyProductLimitUp
