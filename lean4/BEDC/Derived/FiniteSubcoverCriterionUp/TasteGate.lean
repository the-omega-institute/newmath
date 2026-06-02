import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSubcoverCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSubcoverCriterionUp : Type where
  | mk (K E L R Q D H C P N : BHist) : FiniteSubcoverCriterionUp
  deriving DecidableEq

def finiteSubcoverCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSubcoverCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSubcoverCriterionEncodeBHist h

def finiteSubcoverCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSubcoverCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSubcoverCriterionDecodeBHist tail)

private theorem FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem FiniteSubcoverCriterionTasteGate_single_carrier_alignment_mk_congr
    {K K' E E' L L' R R' Q Q' D D' H H' C C' P P' N N' : BHist}
    (hK : K' = K)
    (hE : E' = E)
    (hL : L' = L)
    (hR : R' = R)
    (hQ : Q' = Q)
    (hD : D' = D)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    FiniteSubcoverCriterionUp.mk K' E' L' R' Q' D' H' C' P' N' =
      FiniteSubcoverCriterionUp.mk K E L R Q D H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hE
  cases hL
  cases hR
  cases hQ
  cases hD
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def finiteSubcoverCriterionToEventFlow : FiniteSubcoverCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSubcoverCriterionUp.mk K E L R Q D H C P N =>
      [finiteSubcoverCriterionEncodeBHist K,
        finiteSubcoverCriterionEncodeBHist E,
        finiteSubcoverCriterionEncodeBHist L,
        finiteSubcoverCriterionEncodeBHist R,
        finiteSubcoverCriterionEncodeBHist Q,
        finiteSubcoverCriterionEncodeBHist D,
        finiteSubcoverCriterionEncodeBHist H,
        finiteSubcoverCriterionEncodeBHist C,
        finiteSubcoverCriterionEncodeBHist P,
        finiteSubcoverCriterionEncodeBHist N]

private def finiteSubcoverCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSubcoverCriterionEventAtDefault index rest

def finiteSubcoverCriterionFromEventFlow (ef : EventFlow) :
    Option FiniteSubcoverCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSubcoverCriterionUp.mk
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 0 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 1 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 2 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 3 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 4 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 5 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 6 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 7 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 8 ef))
      (finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEventAtDefault 9 ef)))

private theorem FiniteSubcoverCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteSubcoverCriterionUp,
      finiteSubcoverCriterionFromEventFlow (finiteSubcoverCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K E L R Q D H C P N =>
      exact
        congrArg some
          (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_mk_congr
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode K)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode E)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode L)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode R)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode Q)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode D)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode H)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode C)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode P)
            (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode N))

private theorem FiniteSubcoverCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSubcoverCriterionUp} :
    finiteSubcoverCriterionToEventFlow x = finiteSubcoverCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSubcoverCriterionFromEventFlow (finiteSubcoverCriterionToEventFlow x) =
        finiteSubcoverCriterionFromEventFlow (finiteSubcoverCriterionToEventFlow y) :=
    congrArg finiteSubcoverCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance finiteSubcoverCriterionBHistCarrier :
    BHistCarrier FiniteSubcoverCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSubcoverCriterionToEventFlow
  fromEventFlow := finiteSubcoverCriterionFromEventFlow

instance finiteSubcoverCriterionChapterTasteGate :
    ChapterTasteGate FiniteSubcoverCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSubcoverCriterionFromEventFlow (finiteSubcoverCriterionToEventFlow x) =
      some x
    exact FiniteSubcoverCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteSubcoverCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteSubcoverCriterionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      finiteSubcoverCriterionDecodeBHist (finiteSubcoverCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteSubcoverCriterionUp) ∧
        Nonempty (ChapterTasteGate FiniteSubcoverCriterionUp) ∧
          finiteSubcoverCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteSubcoverCriterionTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro finiteSubcoverCriterionBHistCarrier,
      Nonempty.intro finiteSubcoverCriterionChapterTasteGate,
      rfl⟩

end BEDC.Derived.FiniteSubcoverCriterionUp
