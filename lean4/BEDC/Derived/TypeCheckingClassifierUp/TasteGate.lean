import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeCheckingClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeCheckingClassifierUp : Type where
  | mk (T J E D S R H C P N : BHist) : TypeCheckingClassifierUp
  deriving DecidableEq

def typeCheckingClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeCheckingClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeCheckingClassifierEncodeBHist h

def typeCheckingClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeCheckingClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeCheckingClassifierDecodeBHist tail)

private theorem typeCheckingClassifier_decode_encode :
    ∀ h : BHist,
      typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typeCheckingClassifierFields : TypeCheckingClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingClassifierUp.mk T J E D S R H C P N => [T, J, E, D, S, R, H, C, P, N]

def typeCheckingClassifierToEventFlow : TypeCheckingClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (typeCheckingClassifierFields x).map typeCheckingClassifierEncodeBHist

private def typeCheckingClassifierEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => typeCheckingClassifierEventAt index rest

def typeCheckingClassifierFromEventFlow : EventFlow → Option TypeCheckingClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (TypeCheckingClassifierUp.mk
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 0 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 1 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 2 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 3 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 4 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 5 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 6 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 7 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 8 ef))
        (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEventAt 9 ef)))

private theorem typeCheckingClassifier_round_trip :
    ∀ x : TypeCheckingClassifierUp,
      typeCheckingClassifierFromEventFlow (typeCheckingClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T J E D S R H C P N =>
      change
        some
          (TypeCheckingClassifierUp.mk
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist T))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist J))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist E))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist D))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist S))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist R))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist H))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist C))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist P))
            (typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist N))) =
          some (TypeCheckingClassifierUp.mk T J E D S R H C P N)
      rw [typeCheckingClassifier_decode_encode T, typeCheckingClassifier_decode_encode J,
        typeCheckingClassifier_decode_encode E, typeCheckingClassifier_decode_encode D,
        typeCheckingClassifier_decode_encode S, typeCheckingClassifier_decode_encode R,
        typeCheckingClassifier_decode_encode H, typeCheckingClassifier_decode_encode C,
        typeCheckingClassifier_decode_encode P, typeCheckingClassifier_decode_encode N]

private theorem typeCheckingClassifierToEventFlow_injective
    {x y : TypeCheckingClassifierUp} :
    typeCheckingClassifierToEventFlow x = typeCheckingClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeCheckingClassifierFromEventFlow (typeCheckingClassifierToEventFlow x) =
        typeCheckingClassifierFromEventFlow (typeCheckingClassifierToEventFlow y) :=
    congrArg typeCheckingClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typeCheckingClassifier_round_trip x).symm
      (Eq.trans hread (typeCheckingClassifier_round_trip y)))

instance typeCheckingClassifierBHistCarrier : BHistCarrier TypeCheckingClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeCheckingClassifierToEventFlow
  fromEventFlow := typeCheckingClassifierFromEventFlow

instance typeCheckingClassifierChapterTasteGate : ChapterTasteGate TypeCheckingClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change typeCheckingClassifierFromEventFlow (typeCheckingClassifierToEventFlow x) = some x
    exact typeCheckingClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typeCheckingClassifierToEventFlow_injective heq)

theorem TypeCheckingClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist, typeCheckingClassifierDecodeBHist (typeCheckingClassifierEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier TypeCheckingClassifierUp) ∧
        Nonempty (ChapterTasteGate TypeCheckingClassifierUp) ∧
          typeCheckingClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact typeCheckingClassifier_decode_encode
  constructor
  · exact ⟨typeCheckingClassifierBHistCarrier⟩
  constructor
  · exact ⟨typeCheckingClassifierChapterTasteGate⟩
  · rfl

end BEDC.Derived.TypeCheckingClassifierUp
