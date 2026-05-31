import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationTheoremUp : Type where
  | mk (A M D B G Q U V R E H C P N : BHist) : CauchyCondensationTheoremUp
  deriving DecidableEq

def cauchyCondensationTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationTheoremEncodeBHist h

def cauchyCondensationTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationTheoremDecodeBHist tail)

private theorem CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCondensationTheoremToEventFlow :
    CauchyCondensationTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationTheoremUp.mk A M D B G Q U V R E H C P N =>
      [cauchyCondensationTheoremEncodeBHist A,
        cauchyCondensationTheoremEncodeBHist M,
        cauchyCondensationTheoremEncodeBHist D,
        cauchyCondensationTheoremEncodeBHist B,
        cauchyCondensationTheoremEncodeBHist G,
        cauchyCondensationTheoremEncodeBHist Q,
        cauchyCondensationTheoremEncodeBHist U,
        cauchyCondensationTheoremEncodeBHist V,
        cauchyCondensationTheoremEncodeBHist R,
        cauchyCondensationTheoremEncodeBHist E,
        cauchyCondensationTheoremEncodeBHist H,
        cauchyCondensationTheoremEncodeBHist C,
        cauchyCondensationTheoremEncodeBHist P,
        cauchyCondensationTheoremEncodeBHist N]

private def cauchyCondensationTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCondensationTheoremEventAtDefault index rest

def cauchyCondensationTheoremFromEventFlow
    (ef : EventFlow) : Option CauchyCondensationTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCondensationTheoremUp.mk
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 0 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 1 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 2 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 3 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 4 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 5 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 6 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 7 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 8 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 9 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 10 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 11 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 12 ef))
      (cauchyCondensationTheoremDecodeBHist
        (cauchyCondensationTheoremEventAtDefault 13 ef)))

private theorem CauchyCondensationTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCondensationTheoremUp,
      cauchyCondensationTheoremFromEventFlow
        (cauchyCondensationTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M D B G Q U V R E H C P N =>
      change
        some
          (CauchyCondensationTheoremUp.mk
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist A))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist M))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist D))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist B))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist G))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist Q))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist U))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist V))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist R))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist E))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist H))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist C))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist P))
            (cauchyCondensationTheoremDecodeBHist
              (cauchyCondensationTheoremEncodeBHist N))) =
          some (CauchyCondensationTheoremUp.mk A M D B G Q U V R E H C P N)
      rw [CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode A,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode M,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode D,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode B,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode G,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode Q,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode U,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode V,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode R,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode E,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode H,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode C,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode P,
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCondensationTheoremTasteGate_single_carrier_alignment_injective
    {x y : CauchyCondensationTheoremUp} :
    cauchyCondensationTheoremToEventFlow x =
        cauchyCondensationTheoremToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationTheoremFromEventFlow
          (cauchyCondensationTheoremToEventFlow x) =
        cauchyCondensationTheoremFromEventFlow
          (cauchyCondensationTheoremToEventFlow y) :=
    congrArg cauchyCondensationTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCondensationTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCondensationTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCondensationTheoremBHistCarrier :
    BHistCarrier CauchyCondensationTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationTheoremToEventFlow
  fromEventFlow := cauchyCondensationTheoremFromEventFlow

instance cauchyCondensationTheoremChapterTasteGate :
    ChapterTasteGate CauchyCondensationTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCondensationTheoremFromEventFlow
      (cauchyCondensationTheoremToEventFlow x) = some x
    exact CauchyCondensationTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCondensationTheoremTasteGate_single_carrier_alignment_injective heq)

theorem CauchyCondensationTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCondensationTheoremDecodeBHist
      (cauchyCondensationTheoremEncodeBHist h) = h) ∧
      (∀ x : CauchyCondensationTheoremUp,
        cauchyCondensationTheoremFromEventFlow
          (cauchyCondensationTheoremToEventFlow x) = some x) ∧
        (∀ x y : CauchyCondensationTheoremUp,
          cauchyCondensationTheoremToEventFlow x =
              cauchyCondensationTheoremToEventFlow y →
            x = y) ∧
          cauchyCondensationTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCondensationTheoremTasteGate_single_carrier_alignment_decode,
      CauchyCondensationTheoremTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCondensationTheoremTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCondensationTheoremUp
