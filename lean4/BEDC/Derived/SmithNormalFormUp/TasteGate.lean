import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SmithNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SmithNormalFormUp : Type where
  | mk (M R C D V E U H T P N : BHist) : SmithNormalFormUp
  deriving DecidableEq

def smithNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: smithNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: smithNormalFormEncodeBHist h

def smithNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (smithNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (smithNormalFormDecodeBHist tail)

private theorem SmithNormalFormTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, smithNormalFormDecodeBHist (smithNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def smithNormalFormToEventFlow : SmithNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SmithNormalFormUp.mk M R C D V E U H T P N =>
      [[BMark.b0],
        smithNormalFormEncodeBHist M,
        [BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        smithNormalFormEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        smithNormalFormEncodeBHist N]

private def smithNormalFormEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => smithNormalFormEventAtDefault index rest

def smithNormalFormFromEventFlow (ef : EventFlow) : Option SmithNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SmithNormalFormUp.mk
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 1 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 3 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 5 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 7 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 9 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 11 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 13 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 15 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 17 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 19 ef))
      (smithNormalFormDecodeBHist (smithNormalFormEventAtDefault 21 ef)))

private theorem smithNormalForm_mk_congr
    {M M' R R' C C' D D' V V' E E' U U' H H' T T' P P' N N' : BHist}
    (hM : M' = M) (hR : R' = R) (hC : C' = C) (hD : D' = D)
    (hV : V' = V) (hE : E' = E) (hU : U' = U) (hH : H' = H)
    (hT : T' = T) (hP : P' = P) (hN : N' = N) :
    SmithNormalFormUp.mk M' R' C' D' V' E' U' H' T' P' N' =
      SmithNormalFormUp.mk M R C D V E U H T P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hR
  cases hC
  cases hD
  cases hV
  cases hE
  cases hU
  cases hH
  cases hT
  cases hP
  cases hN
  rfl

private theorem SmithNormalFormTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SmithNormalFormUp,
      smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R C D V E U H T P N =>
      exact
        congrArg some
          (smithNormalForm_mk_congr
            (SmithNormalFormTasteGate_single_carrier_alignment_decode M)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode R)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode C)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode D)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode V)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode E)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode U)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode H)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode T)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode P)
            (SmithNormalFormTasteGate_single_carrier_alignment_decode N))

private theorem smithNormalFormToEventFlow_injective {x y : SmithNormalFormUp} :
    smithNormalFormToEventFlow x = smithNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) =
        smithNormalFormFromEventFlow (smithNormalFormToEventFlow y) :=
    congrArg smithNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SmithNormalFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SmithNormalFormTasteGate_single_carrier_alignment_round_trip y)))

instance smithNormalFormBHistCarrier : BHistCarrier SmithNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := smithNormalFormToEventFlow
  fromEventFlow := smithNormalFormFromEventFlow

instance smithNormalFormChapterTasteGate : ChapterTasteGate SmithNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) = some x
    exact SmithNormalFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (smithNormalFormToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SmithNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  smithNormalFormChapterTasteGate

theorem SmithNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist, smithNormalFormDecodeBHist (smithNormalFormEncodeBHist h) = h) ∧
      (∀ x : SmithNormalFormUp,
        smithNormalFormFromEventFlow (smithNormalFormToEventFlow x) = some x) ∧
      (∀ x y : SmithNormalFormUp,
        smithNormalFormToEventFlow x = smithNormalFormToEventFlow y → x = y) ∧
      smithNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SmithNormalFormTasteGate_single_carrier_alignment_decode
  constructor
  · exact SmithNormalFormTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact smithNormalFormToEventFlow_injective heq
  · rfl

end BEDC.Derived.SmithNormalFormUp
