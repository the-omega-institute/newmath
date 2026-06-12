import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletenessTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletenessTheoremUp : Type where
  | mk (D S Q L U A R H C P N : BHist) : CauchyCompletenessTheoremUp
  deriving DecidableEq

def cauchyCompletenessTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletenessTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletenessTheoremEncodeBHist h

def cauchyCompletenessTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletenessTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletenessTheoremDecodeBHist tail)

private theorem CauchyCompletenessTheoremTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletenessTheoremFields : CauchyCompletenessTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletenessTheoremUp.mk D S Q L U A R H C P N =>
      [D, S, Q, L, U, A, R, H, C, P, N]

def cauchyCompletenessTheoremToEventFlow :
    CauchyCompletenessTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletenessTheoremFields x).map
      cauchyCompletenessTheoremEncodeBHist

private def cauchyCompletenessTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletenessTheoremEventAtDefault index rest

def cauchyCompletenessTheoremFromEventFlow :
    EventFlow → Option CauchyCompletenessTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletenessTheoremUp.mk
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 0 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 1 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 2 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 3 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 4 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 5 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 6 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 7 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 8 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 9 ef))
        (cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEventAtDefault 10 ef)))

private theorem CauchyCompletenessTheoremTasteGate_round_trip :
    ∀ x : CauchyCompletenessTheoremUp,
      cauchyCompletenessTheoremFromEventFlow
          (cauchyCompletenessTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D S Q L U A R H C P N =>
      change
        some
          (CauchyCompletenessTheoremUp.mk
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist D))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist S))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist Q))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist L))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist U))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist A))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist R))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist H))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist C))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist P))
            (cauchyCompletenessTheoremDecodeBHist
              (cauchyCompletenessTheoremEncodeBHist N))) =
          some (CauchyCompletenessTheoremUp.mk D S Q L U A R H C P N)
      rw [CauchyCompletenessTheoremTasteGate_decode_encode D,
        CauchyCompletenessTheoremTasteGate_decode_encode S,
        CauchyCompletenessTheoremTasteGate_decode_encode Q,
        CauchyCompletenessTheoremTasteGate_decode_encode L,
        CauchyCompletenessTheoremTasteGate_decode_encode U,
        CauchyCompletenessTheoremTasteGate_decode_encode A,
        CauchyCompletenessTheoremTasteGate_decode_encode R,
        CauchyCompletenessTheoremTasteGate_decode_encode H,
        CauchyCompletenessTheoremTasteGate_decode_encode C,
        CauchyCompletenessTheoremTasteGate_decode_encode P,
        CauchyCompletenessTheoremTasteGate_decode_encode N]

private theorem CauchyCompletenessTheoremTasteGate_toEventFlow_injective
    {x y : CauchyCompletenessTheoremUp} :
    cauchyCompletenessTheoremToEventFlow x =
        cauchyCompletenessTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletenessTheoremFromEventFlow
          (cauchyCompletenessTheoremToEventFlow x) =
        cauchyCompletenessTheoremFromEventFlow
          (cauchyCompletenessTheoremToEventFlow y) :=
    congrArg cauchyCompletenessTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletenessTheoremTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyCompletenessTheoremTasteGate_round_trip y)))

instance cauchyCompletenessTheoremBHistCarrier :
    BHistCarrier CauchyCompletenessTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletenessTheoremToEventFlow
  fromEventFlow := cauchyCompletenessTheoremFromEventFlow

instance cauchyCompletenessTheoremChapterTasteGate :
    ChapterTasteGate CauchyCompletenessTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletenessTheoremFromEventFlow
          (cauchyCompletenessTheoremToEventFlow x) = some x
    exact CauchyCompletenessTheoremTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletenessTheoremTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletenessTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletenessTheoremChapterTasteGate

theorem CauchyCompletenessTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyCompletenessTheoremDecodeBHist
          (cauchyCompletenessTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletenessTheoremUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletenessTheoremUp) ∧
          cauchyCompletenessTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletenessTheoremTasteGate_decode_encode,
      ⟨cauchyCompletenessTheoremBHistCarrier⟩,
      ⟨cauchyCompletenessTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletenessTheoremUp
