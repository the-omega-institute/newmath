import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectiveSubcategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectiveSubcategoryUp : Type where
  | mk (S M J U Q E Z T H C P N : BHist) : CauchyCompletionReflectiveSubcategoryUp
  deriving DecidableEq

def cauchyCompletionReflectiveSubcategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectiveSubcategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectiveSubcategoryEncodeBHist h

def cauchyCompletionReflectiveSubcategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectiveSubcategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectiveSubcategoryDecodeBHist tail)

private theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectiveSubcategoryToEventFlow :
    CauchyCompletionReflectiveSubcategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectiveSubcategoryUp.mk S M J U Q E Z T H C P N =>
      [[BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist S,
        [BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionReflectiveSubcategoryEncodeBHist N]

private def cauchyCompletionReflectiveSubcategoryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionReflectiveSubcategoryEventAtDefault index rest

def cauchyCompletionReflectiveSubcategoryFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionReflectiveSubcategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionReflectiveSubcategoryUp.mk
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 1 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 3 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 5 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 7 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 9 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 11 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 13 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 15 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 17 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 19 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 21 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 23 ef)))

private theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionReflectiveSubcategoryUp,
      cauchyCompletionReflectiveSubcategoryFromEventFlow
        (cauchyCompletionReflectiveSubcategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M J U Q E Z T H C P N =>
      change
        some
          (CauchyCompletionReflectiveSubcategoryUp.mk
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist S))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist M))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist J))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist U))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist Q))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist E))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist Z))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist T))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist H))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist C))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist P))
            (cauchyCompletionReflectiveSubcategoryDecodeBHist
              (cauchyCompletionReflectiveSubcategoryEncodeBHist N))) =
          some (CauchyCompletionReflectiveSubcategoryUp.mk S M J U Q E Z T H C P N)
      rw [CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode M,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode J,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode U,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode Q,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode Z,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionReflectiveSubcategoryUp} :
    cauchyCompletionReflectiveSubcategoryToEventFlow x =
      cauchyCompletionReflectiveSubcategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectiveSubcategoryFromEventFlow
          (cauchyCompletionReflectiveSubcategoryToEventFlow x) =
        cauchyCompletionReflectiveSubcategoryFromEventFlow
          (cauchyCompletionReflectiveSubcategoryToEventFlow y) :=
    congrArg cauchyCompletionReflectiveSubcategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionReflectiveSubcategoryBHistCarrier :
    BHistCarrier CauchyCompletionReflectiveSubcategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectiveSubcategoryToEventFlow
  fromEventFlow := cauchyCompletionReflectiveSubcategoryFromEventFlow

instance cauchyCompletionReflectiveSubcategoryChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectiveSubcategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectiveSubcategoryFromEventFlow
        (cauchyCompletionReflectiveSubcategoryToEventFlow x) = some x
    exact CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate CauchyCompletionReflectiveSubcategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionReflectiveSubcategoryChapterTasteGate

theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionReflectiveSubcategoryUp,
        cauchyCompletionReflectiveSubcategoryFromEventFlow
          (cauchyCompletionReflectiveSubcategoryToEventFlow x) = some x) ∧
      Nonempty (ChapterTasteGate CauchyCompletionReflectiveSubcategoryUp) ∧
        cauchyCompletionReflectiveSubcategoryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode,
      CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip,
      ⟨cauchyCompletionReflectiveSubcategoryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectiveSubcategoryUp
