import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCompletenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCompletenessUp : Type where
  | mk (B N C W R E H T P Q : BHist) : NestedIntervalCompletenessUp
  deriving DecidableEq

def nestedIntervalCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalCompletenessEncodeBHist h

def nestedIntervalCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalCompletenessDecodeBHist tail)

private theorem nestedIntervalCompleteness_decode_encode :
    ∀ h : BHist,
      nestedIntervalCompletenessDecodeBHist
          (nestedIntervalCompletenessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalCompletenessFields :
    NestedIntervalCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalCompletenessUp.mk B N C W R E H T P Q => [B, N, C, W, R, E, H, T, P, Q]

def nestedIntervalCompletenessToEventFlow :
    NestedIntervalCompletenessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (nestedIntervalCompletenessFields x).map nestedIntervalCompletenessEncodeBHist

def nestedIntervalCompletenessFromEventFlow :
    EventFlow → Option NestedIntervalCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | B :: N :: C :: W :: R :: E :: H :: T :: P :: Q :: [] =>
      some
        (NestedIntervalCompletenessUp.mk
          (nestedIntervalCompletenessDecodeBHist B)
          (nestedIntervalCompletenessDecodeBHist N)
          (nestedIntervalCompletenessDecodeBHist C)
          (nestedIntervalCompletenessDecodeBHist W)
          (nestedIntervalCompletenessDecodeBHist R)
          (nestedIntervalCompletenessDecodeBHist E)
          (nestedIntervalCompletenessDecodeBHist H)
          (nestedIntervalCompletenessDecodeBHist T)
          (nestedIntervalCompletenessDecodeBHist P)
          (nestedIntervalCompletenessDecodeBHist Q))
  | _ => none

private theorem nestedIntervalCompleteness_round_trip :
    ∀ x : NestedIntervalCompletenessUp,
      nestedIntervalCompletenessFromEventFlow
          (nestedIntervalCompletenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B N C W R E H T P Q =>
      simp only [nestedIntervalCompletenessToEventFlow, nestedIntervalCompletenessFields,
        nestedIntervalCompletenessFromEventFlow, List.map_cons, List.map_nil,
        nestedIntervalCompleteness_decode_encode]

private theorem nestedIntervalCompletenessToEventFlow_injective
    {x y : NestedIntervalCompletenessUp} :
    nestedIntervalCompletenessToEventFlow x = nestedIntervalCompletenessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          nestedIntervalCompletenessFromEventFlow
            (nestedIntervalCompletenessToEventFlow x) :=
        (nestedIntervalCompleteness_round_trip x).symm
      _ =
          nestedIntervalCompletenessFromEventFlow
            (nestedIntervalCompletenessToEventFlow y) :=
        congrArg nestedIntervalCompletenessFromEventFlow hxy
      _ = some y := nestedIntervalCompleteness_round_trip y
  exact Option.some.inj optionEq

instance nestedIntervalCompletenessBHistCarrier :
    BHistCarrier NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalCompletenessToEventFlow
  fromEventFlow := nestedIntervalCompletenessFromEventFlow

instance nestedIntervalCompletenessChapterTasteGate :
    ChapterTasteGate NestedIntervalCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalCompletenessFromEventFlow
          (nestedIntervalCompletenessToEventFlow x) =
        some x
    exact nestedIntervalCompleteness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalCompletenessToEventFlow_injective heq)

private theorem nestedIntervalCompleteness_mk_congr
    {B0 N0 C0 W0 R0 E0 H0 T0 P0 Q0 B N C W R E H T P Q : BHist}
    (hB : B0 = B) (hN : N0 = N) (hC : C0 = C) (hW : W0 = W) (hR : R0 = R)
    (hE : E0 = E) (hH : H0 = H) (hT : T0 = T) (hP : P0 = P) (hQ : Q0 = Q) :
    NestedIntervalCompletenessUp.mk B0 N0 C0 W0 R0 E0 H0 T0 P0 Q0 =
      NestedIntervalCompletenessUp.mk B N C W R E H T P Q := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hN
  cases hC
  cases hW
  cases hR
  cases hE
  cases hH
  cases hT
  cases hP
  cases hQ
  rfl

theorem NestedIntervalCompletenessTasteGate_single_carrier_alignment :
    nestedIntervalCompletenessDecodeBHist
        (nestedIntervalCompletenessEncodeBHist BHist.Empty) =
      BHist.Empty ∧
      (∀ h : BHist,
          nestedIntervalCompletenessDecodeBHist
            (nestedIntervalCompletenessEncodeBHist h) =
          h) ∧
        (∀ B N C W R E H T P Q : BHist,
          some
              (NestedIntervalCompletenessUp.mk
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist B))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist N))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist C))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist W))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist R))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist E))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist H))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist T))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist P))
                (nestedIntervalCompletenessDecodeBHist (nestedIntervalCompletenessEncodeBHist Q))) =
            some (NestedIntervalCompletenessUp.mk B N C W R E H T P Q)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · rfl
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · intro B N C W R E H T P Q
    exact congrArg some
      (nestedIntervalCompleteness_mk_congr
        (nestedIntervalCompleteness_decode_encode B)
        (nestedIntervalCompleteness_decode_encode N)
        (nestedIntervalCompleteness_decode_encode C)
        (nestedIntervalCompleteness_decode_encode W)
        (nestedIntervalCompleteness_decode_encode R)
        (nestedIntervalCompleteness_decode_encode E)
        (nestedIntervalCompleteness_decode_encode H)
        (nestedIntervalCompleteness_decode_encode T)
        (nestedIntervalCompleteness_decode_encode P)
        (nestedIntervalCompleteness_decode_encode Q))

end BEDC.Derived.NestedIntervalCompletenessUp.TasteGate
