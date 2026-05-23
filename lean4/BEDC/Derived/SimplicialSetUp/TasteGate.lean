import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SimplicialSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SimplicialSetUp : Type where
  | mk (functor simplex face degeneracy package provenance ledger : BHist) : SimplicialSetUp
  deriving DecidableEq

def simplicialSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: simplicialSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: simplicialSetEncodeBHist h

def simplicialSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (simplicialSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (simplicialSetDecodeBHist tail)

private theorem simplicialSet_decode_encode :
    ∀ h : BHist, simplicialSetDecodeBHist (simplicialSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def simplicialSetToEventFlow : SimplicialSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | SimplicialSetUp.mk functor simplex face degeneracy package provenance ledger =>
      [simplicialSetEncodeBHist functor,
        simplicialSetEncodeBHist simplex,
        simplicialSetEncodeBHist face,
        simplicialSetEncodeBHist degeneracy,
        simplicialSetEncodeBHist package,
        simplicialSetEncodeBHist provenance,
        simplicialSetEncodeBHist ledger]

def simplicialSetFromEventFlow : EventFlow → Option SimplicialSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | functor :: rest0 =>
      match rest0 with
      | [] => none
      | simplex :: rest1 =>
          match rest1 with
          | [] => none
          | face :: rest2 =>
              match rest2 with
              | [] => none
              | degeneracy :: rest3 =>
                  match rest3 with
                  | [] => none
                  | package :: rest4 =>
                      match rest4 with
                      | [] => none
                      | provenance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (SimplicialSetUp.mk
                                      (simplicialSetDecodeBHist functor)
                                      (simplicialSetDecodeBHist simplex)
                                      (simplicialSetDecodeBHist face)
                                      (simplicialSetDecodeBHist degeneracy)
                                      (simplicialSetDecodeBHist package)
                                      (simplicialSetDecodeBHist provenance)
                                      (simplicialSetDecodeBHist ledger))
                              | _ :: _ => none

private theorem simplicialSet_round_trip :
    ∀ x : SimplicialSetUp,
      simplicialSetFromEventFlow (simplicialSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk functor simplex face degeneracy package provenance ledger =>
      change
        some
          (SimplicialSetUp.mk
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist functor))
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist simplex))
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist face))
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist degeneracy))
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist package))
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist provenance))
            (simplicialSetDecodeBHist (simplicialSetEncodeBHist ledger))) =
          some
            (SimplicialSetUp.mk functor simplex face degeneracy package provenance ledger)
      rw [simplicialSet_decode_encode functor, simplicialSet_decode_encode simplex,
        simplicialSet_decode_encode face, simplicialSet_decode_encode degeneracy,
        simplicialSet_decode_encode package, simplicialSet_decode_encode provenance,
        simplicialSet_decode_encode ledger]

private theorem simplicialSetToEventFlow_injective {x y : SimplicialSetUp} :
    simplicialSetToEventFlow x = simplicialSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      simplicialSetFromEventFlow (simplicialSetToEventFlow x) =
        simplicialSetFromEventFlow (simplicialSetToEventFlow y) :=
    congrArg simplicialSetFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (simplicialSet_round_trip x).symm
      (Eq.trans hread (simplicialSet_round_trip y))
  cases hsome
  rfl

instance simplicialSetBHistCarrier : BHistCarrier SimplicialSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := simplicialSetToEventFlow
  fromEventFlow := simplicialSetFromEventFlow

instance simplicialSetChapterTasteGate : ChapterTasteGate SimplicialSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change simplicialSetFromEventFlow (simplicialSetToEventFlow x) = some x
    exact simplicialSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (simplicialSetToEventFlow_injective heq)

theorem SimplicialSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, simplicialSetDecodeBHist (simplicialSetEncodeBHist h) = h) ∧
      (∀ x : SimplicialSetUp,
        simplicialSetFromEventFlow (simplicialSetToEventFlow x) = some x) ∧
        (∀ x y : SimplicialSetUp,
          simplicialSetToEventFlow x = simplicialSetToEventFlow y → x = y) ∧
      simplicialSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨simplicialSet_decode_encode, simplicialSet_round_trip,
      fun x y heq => simplicialSetToEventFlow_injective heq, rfl⟩

end BEDC.Derived.SimplicialSetUp
