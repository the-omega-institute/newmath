import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# FiniteWindowBaireCategoryUp TasteGate carrier.
-/

namespace BEDC.Derived.FiniteWindowBaireCategoryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite Baire-category window packet with the twelve displayed BEDC rows. -/
inductive FiniteWindowBaireCategoryUp : Type where
  | mk :
      (metric denseWindow radiusLedger centerLedger streamSchedule regularReadback realSeal
        completionTransport transport replay provenance name : BHist) →
      FiniteWindowBaireCategoryUp
  deriving DecidableEq

def finiteWindowBaireCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowBaireCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowBaireCategoryEncodeBHist h

def finiteWindowBaireCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowBaireCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowBaireCategoryDecodeBHist tail)

private theorem finiteWindowBaireCategory_decode_encode :
    ∀ h : BHist,
      finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteWindowBaireCategoryFields : FiniteWindowBaireCategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowBaireCategoryUp.mk M U D Q S R E T H C P N =>
      [M, U, D, Q, S, R, E, T, H, C, P, N]

def finiteWindowBaireCategoryToEventFlow : FiniteWindowBaireCategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteWindowBaireCategoryFields x).map finiteWindowBaireCategoryEncodeBHist

private def finiteWindowBaireCategoryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteWindowBaireCategoryEventAt index rest

def finiteWindowBaireCategoryFromEventFlow (ef : EventFlow) :
    Option FiniteWindowBaireCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteWindowBaireCategoryUp.mk
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 0 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 1 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 2 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 3 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 4 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 5 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 6 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 7 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 8 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 9 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 10 ef))
      (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEventAt 11 ef)))

private theorem finiteWindowBaireCategory_round_trip :
    ∀ x : FiniteWindowBaireCategoryUp,
      finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U D Q S R E T H C P N =>
      change
        some
          (FiniteWindowBaireCategoryUp.mk
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist M))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist U))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist D))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist Q))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist S))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist R))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist E))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist T))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist H))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist C))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist P))
            (finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist N))) =
          some (FiniteWindowBaireCategoryUp.mk M U D Q S R E T H C P N)
      rw [finiteWindowBaireCategory_decode_encode M, finiteWindowBaireCategory_decode_encode U,
        finiteWindowBaireCategory_decode_encode D, finiteWindowBaireCategory_decode_encode Q,
        finiteWindowBaireCategory_decode_encode S, finiteWindowBaireCategory_decode_encode R,
        finiteWindowBaireCategory_decode_encode E, finiteWindowBaireCategory_decode_encode T,
        finiteWindowBaireCategory_decode_encode H, finiteWindowBaireCategory_decode_encode C,
        finiteWindowBaireCategory_decode_encode P, finiteWindowBaireCategory_decode_encode N]

private theorem finiteWindowBaireCategoryToEventFlow_injective
    {x y : FiniteWindowBaireCategoryUp} :
    finiteWindowBaireCategoryToEventFlow x = finiteWindowBaireCategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) =
        finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow y) :=
    congrArg finiteWindowBaireCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteWindowBaireCategory_round_trip x).symm
      (Eq.trans hread (finiteWindowBaireCategory_round_trip y)))

instance finiteWindowBaireCategoryBHistCarrier : BHistCarrier FiniteWindowBaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowBaireCategoryToEventFlow
  fromEventFlow := finiteWindowBaireCategoryFromEventFlow

instance finiteWindowBaireCategoryChapterTasteGate :
    ChapterTasteGate FiniteWindowBaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteWindowBaireCategoryFromEventFlow (finiteWindowBaireCategoryToEventFlow x) =
      some x
    exact finiteWindowBaireCategory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowBaireCategoryToEventFlow_injective heq)

theorem FiniteWindowBaireCategoryTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteWindowBaireCategoryUp) ∧
      Nonempty (ChapterTasteGate FiniteWindowBaireCategoryUp) ∧
        (∀ h : BHist,
          finiteWindowBaireCategoryDecodeBHist (finiteWindowBaireCategoryEncodeBHist h) = h) ∧
          (∀ x : FiniteWindowBaireCategoryUp,
            finiteWindowBaireCategoryFromEventFlow
              (finiteWindowBaireCategoryToEventFlow x) = some x) ∧
            finiteWindowBaireCategoryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨finiteWindowBaireCategoryBHistCarrier⟩,
      ⟨finiteWindowBaireCategoryChapterTasteGate⟩,
      finiteWindowBaireCategory_decode_encode,
      finiteWindowBaireCategory_round_trip,
      rfl⟩

end BEDC.Derived.FiniteWindowBaireCategoryUp.TasteGate
