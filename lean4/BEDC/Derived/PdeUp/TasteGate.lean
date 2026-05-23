import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PdeUp : Type where
  | mk (manifold derivative relation boundary provenance : BHist) : PdeUp
  deriving DecidableEq

def pdeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pdeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pdeEncodeBHist h

def pdeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pdeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pdeDecodeBHist tail)

private theorem pdeDecodeBHist_encode :
    ∀ h : BHist, pdeDecodeBHist (pdeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def pdeToEventFlow : PdeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PdeUp.mk manifold derivative relation boundary provenance =>
      [pdeEncodeBHist manifold, pdeEncodeBHist derivative, pdeEncodeBHist relation,
        pdeEncodeBHist boundary, pdeEncodeBHist provenance]

private def pdeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pdeEventAt index rest

def pdeFromEventFlow (ef : EventFlow) : Option PdeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PdeUp.mk
      (pdeDecodeBHist (pdeEventAt 0 ef))
      (pdeDecodeBHist (pdeEventAt 1 ef))
      (pdeDecodeBHist (pdeEventAt 2 ef))
      (pdeDecodeBHist (pdeEventAt 3 ef))
      (pdeDecodeBHist (pdeEventAt 4 ef)))

private theorem pde_round_trip :
    ∀ x : PdeUp, pdeFromEventFlow (pdeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk manifold derivative relation boundary provenance =>
      change
        some
            (PdeUp.mk
              (pdeDecodeBHist (pdeEncodeBHist manifold))
              (pdeDecodeBHist (pdeEncodeBHist derivative))
              (pdeDecodeBHist (pdeEncodeBHist relation))
              (pdeDecodeBHist (pdeEncodeBHist boundary))
              (pdeDecodeBHist (pdeEncodeBHist provenance))) =
          some (PdeUp.mk manifold derivative relation boundary provenance)
      rw [pdeDecodeBHist_encode manifold, pdeDecodeBHist_encode derivative,
        pdeDecodeBHist_encode relation, pdeDecodeBHist_encode boundary,
        pdeDecodeBHist_encode provenance]

private theorem pdeToEventFlow_injective {x y : PdeUp} :
    pdeToEventFlow x = pdeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : pdeFromEventFlow (pdeToEventFlow x) = pdeFromEventFlow (pdeToEventFlow y) :=
    congrArg pdeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pde_round_trip x).symm (Eq.trans hread (pde_round_trip y)))

instance pdeBHistCarrier : BHistCarrier PdeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pdeToEventFlow
  fromEventFlow := pdeFromEventFlow

instance pdeChapterTasteGate : ChapterTasteGate PdeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pdeFromEventFlow (pdeToEventFlow x) = some x
    exact pde_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pdeToEventFlow_injective heq)

theorem PdeTasteGate_single_carrier_alignment :
    (forall h : BHist, pdeDecodeBHist (pdeEncodeBHist h) = h) ∧
      (forall x : PdeUp, pdeFromEventFlow (pdeToEventFlow x) = some x) ∧
        (forall x y : PdeUp, pdeToEventFlow x = pdeToEventFlow y -> x = y) ∧
          pdeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact pdeDecodeBHist_encode
  · constructor
    · exact pde_round_trip
    · constructor
      · intro x y
        exact pdeToEventFlow_injective
      · rfl

end BEDC.Derived.PdeUp
