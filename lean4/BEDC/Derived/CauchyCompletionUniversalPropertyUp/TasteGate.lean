import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionUniversalPropertyUp : Type where
  | mk (D K T F E L H C P N : BHist) :
      CauchyCompletionUniversalPropertyUp
  deriving DecidableEq

def cauchyCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUniversalPropertyEncodeBHist h

def cauchyCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUniversalPropertyDecodeBHist tail)

private theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionUniversalPropertyFields :
    CauchyCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N =>
      [D, K, T, F, E, L, H, C, P, N]

def cauchyCompletionUniversalPropertyToEventFlow :
    CauchyCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionUniversalPropertyFields x).map
      cauchyCompletionUniversalPropertyEncodeBHist

private def cauchyCompletionUniversalPropertyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionUniversalPropertyEventAtDefault index rest

def cauchyCompletionUniversalPropertyFromEventFlow :
    EventFlow → Option CauchyCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionUniversalPropertyUp.mk
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 0 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 1 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 2 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 3 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 4 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 5 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 6 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 7 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 8 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 9 ef)))

private theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionUniversalPropertyUp,
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D K T F E L H C P N =>
      change
        some
            (CauchyCompletionUniversalPropertyUp.mk
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist D))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist K))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist T))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist F))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist E))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist L))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist H))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist C))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist P))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist N))) =
          some (CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N)
      rw [CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode K,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode F,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode L,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionUniversalPropertyUp} :
    cauchyCompletionUniversalPropertyToEventFlow x =
        cauchyCompletionUniversalPropertyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow y) :=
    congrArg cauchyCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionUniversalPropertyBHistCarrier :
    BHistCarrier CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUniversalPropertyToEventFlow
  fromEventFlow := cauchyCompletionUniversalPropertyFromEventFlow

instance cauchyCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        some x
    exact CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ D K T F E L H C P N : BHist,
        cauchyCompletionUniversalPropertyFields
          (CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N) =
            [D, K, T, F, E, L, H, C, P, N]) ∧
      cauchyCompletionUniversalPropertyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro D K T F E L H C P N
    rfl
  · rfl

end BEDC.Derived.CauchyCompletionUniversalPropertyUp
