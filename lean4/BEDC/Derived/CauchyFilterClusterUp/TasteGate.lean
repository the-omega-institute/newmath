import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterClusterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterClusterUp : Type where
  | mk (F M U W Q S D E H C P N : BHist) : CauchyFilterClusterUp
  deriving DecidableEq

def cauchyFilterClusterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterClusterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterClusterEncodeBHist h

def cauchyFilterClusterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterClusterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterClusterDecodeBHist tail)

private theorem CauchyFilterClusterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterClusterFields : CauchyFilterClusterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterClusterUp.mk F M U W Q S D E H C P N => [F, M, U, W, Q, S, D, E, H, C, P, N]

def cauchyFilterClusterToEventFlow : CauchyFilterClusterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyFilterClusterEncodeBHist (cauchyFilterClusterFields x)

private def cauchyFilterClusterRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyFilterClusterRawAt n rest

private def cauchyFilterClusterLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyFilterClusterLengthEq n rest

def cauchyFilterClusterFromEventFlow : EventFlow → Option CauchyFilterClusterUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyFilterClusterLengthEq 12 flow with
      | true =>
          some
            (CauchyFilterClusterUp.mk
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 0 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 1 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 2 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 3 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 4 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 5 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 6 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 7 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 8 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 9 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 10 flow))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterRawAt 11 flow)))
      | false => none

private theorem CauchyFilterClusterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterClusterUp,
      cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M U W Q S D E H C P N =>
      change
        some
            (CauchyFilterClusterUp.mk
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist F))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist M))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist U))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist W))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist Q))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist S))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist D))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist E))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist H))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist C))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist P))
              (cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist N))) =
          some (CauchyFilterClusterUp.mk F M U W Q S D E H C P N)
      rw [CauchyFilterClusterTasteGate_single_carrier_alignment_decode F,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode M,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode U,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode W,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode Q,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode S,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode D,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode E,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode H,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode C,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode P,
        CauchyFilterClusterTasteGate_single_carrier_alignment_decode N]

private theorem CauchyFilterClusterTasteGate_single_carrier_alignment_injective
    {x y : CauchyFilterClusterUp}
    (h : cauchyFilterClusterToEventFlow x = cauchyFilterClusterToEventFlow y) :
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  have hread :
      cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) =
        cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow y) :=
    congrArg cauchyFilterClusterFromEventFlow h
  exact Option.some.inj
    (Eq.trans
      (CauchyFilterClusterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyFilterClusterTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterClusterBHistCarrier : BHistCarrier CauchyFilterClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterClusterToEventFlow
  fromEventFlow := cauchyFilterClusterFromEventFlow

instance cauchyFilterClusterChapterTasteGate :
    ChapterTasteGate CauchyFilterClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterClusterFromEventFlow (cauchyFilterClusterToEventFlow x) = some x
    exact CauchyFilterClusterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterClusterTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CauchyFilterClusterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterClusterChapterTasteGate

theorem CauchyFilterClusterTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterClusterDecodeBHist (cauchyFilterClusterEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate CauchyFilterClusterUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyFilterClusterTasteGate_single_carrier_alignment_decode,
      Nonempty.intro cauchyFilterClusterChapterTasteGate⟩

end BEDC.Derived.CauchyFilterClusterUp
