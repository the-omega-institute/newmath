import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionStableReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionStableReflectionUp : Type where
  | mk (F U S Q E H C P N : BHist) : CauchyCompletionStableReflectionUp
  deriving DecidableEq

def cauchyCompletionStableReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionStableReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionStableReflectionEncodeBHist h

def cauchyCompletionStableReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionStableReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionStableReflectionDecodeBHist tail)

private theorem cauchyCompletionStableReflectionDecode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionStableReflectionFields :
    CauchyCompletionStableReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionStableReflectionUp.mk F U S Q E H C P N => [F, U, S, Q, E, H, C, P, N]

def cauchyCompletionStableReflectionToEventFlow :
    CauchyCompletionStableReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionStableReflectionFields x).map
        cauchyCompletionStableReflectionEncodeBHist

private def cauchyCompletionStableReflectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionStableReflectionEventAt index rest

def cauchyCompletionStableReflectionFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionStableReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionStableReflectionUp.mk
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 0 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 1 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 2 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 3 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 4 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 5 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 6 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 7 ef))
      (cauchyCompletionStableReflectionDecodeBHist
        (cauchyCompletionStableReflectionEventAt 8 ef)))

private theorem cauchyCompletionStableReflection_round_trip
    (x : CauchyCompletionStableReflectionUp) :
    cauchyCompletionStableReflectionFromEventFlow
        (cauchyCompletionStableReflectionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F U S Q E H C P N =>
      change
        some
          (CauchyCompletionStableReflectionUp.mk
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist F))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist U))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist S))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist Q))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist E))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist H))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist C))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist P))
            (cauchyCompletionStableReflectionDecodeBHist
              (cauchyCompletionStableReflectionEncodeBHist N))) =
          some (CauchyCompletionStableReflectionUp.mk F U S Q E H C P N)
      rw [cauchyCompletionStableReflectionDecode_encode_bhist F,
        cauchyCompletionStableReflectionDecode_encode_bhist U,
        cauchyCompletionStableReflectionDecode_encode_bhist S,
        cauchyCompletionStableReflectionDecode_encode_bhist Q,
        cauchyCompletionStableReflectionDecode_encode_bhist E,
        cauchyCompletionStableReflectionDecode_encode_bhist H,
        cauchyCompletionStableReflectionDecode_encode_bhist C,
        cauchyCompletionStableReflectionDecode_encode_bhist P,
        cauchyCompletionStableReflectionDecode_encode_bhist N]

private theorem cauchyCompletionStableReflectionToEventFlow_injective
    {x y : CauchyCompletionStableReflectionUp} :
    cauchyCompletionStableReflectionToEventFlow x =
      cauchyCompletionStableReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionStableReflectionFromEventFlow
          (cauchyCompletionStableReflectionToEventFlow x) =
        cauchyCompletionStableReflectionFromEventFlow
          (cauchyCompletionStableReflectionToEventFlow y) :=
    congrArg cauchyCompletionStableReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionStableReflection_round_trip x).symm
      (Eq.trans hread (cauchyCompletionStableReflection_round_trip y)))

instance cauchyCompletionStableReflectionBHistCarrier :
    BHistCarrier CauchyCompletionStableReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionStableReflectionToEventFlow
  fromEventFlow := cauchyCompletionStableReflectionFromEventFlow

instance cauchyCompletionStableReflectionChapterTasteGate :
    ChapterTasteGate CauchyCompletionStableReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionStableReflectionFromEventFlow
      (cauchyCompletionStableReflectionToEventFlow x) = some x
    exact cauchyCompletionStableReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionStableReflectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionStableReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionStableReflectionChapterTasteGate

theorem CauchyCompletionStableReflectionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyCompletionStableReflectionUp) ∧
      Nonempty (ChapterTasteGate CauchyCompletionStableReflectionUp) ∧
        ∀ x y : CauchyCompletionStableReflectionUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyCompletionStableReflectionBHistCarrier⟩
  · constructor
    · exact ⟨cauchyCompletionStableReflectionChapterTasteGate⟩
    · intro x y heq
      change cauchyCompletionStableReflectionToEventFlow x =
        cauchyCompletionStableReflectionToEventFlow y at heq
      exact cauchyCompletionStableReflectionToEventFlow_injective heq

end BEDC.Derived.CauchyCompletionStableReflectionUp
