import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealTriangleInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealTriangleInequalityUp : Type where
  | mk : (A B M D W H C P N : BHist) → RealTriangleInequalityUp
  deriving DecidableEq

def realTriangleInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realTriangleInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realTriangleInequalityEncodeBHist h

def realTriangleInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realTriangleInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realTriangleInequalityDecodeBHist tail)

private theorem realTriangleInequality_decode_encode_bhist :
    ∀ h : BHist,
      realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realTriangleInequalityFields : RealTriangleInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealTriangleInequalityUp.mk A B M D W H C P N => [A, B, M, D, W, H, C, P, N]

def realTriangleInequalityToEventFlow : RealTriangleInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realTriangleInequalityEncodeBHist (realTriangleInequalityFields x)

def realTriangleInequalityFromEventFlow : EventFlow → Option RealTriangleInequalityUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: B :: M :: D :: W :: H :: C :: P :: N :: [] =>
      some
        (RealTriangleInequalityUp.mk
          (realTriangleInequalityDecodeBHist A)
          (realTriangleInequalityDecodeBHist B)
          (realTriangleInequalityDecodeBHist M)
          (realTriangleInequalityDecodeBHist D)
          (realTriangleInequalityDecodeBHist W)
          (realTriangleInequalityDecodeBHist H)
          (realTriangleInequalityDecodeBHist C)
          (realTriangleInequalityDecodeBHist P)
          (realTriangleInequalityDecodeBHist N))
  | _ => none

private theorem realTriangleInequality_round_trip :
    ∀ x : RealTriangleInequalityUp,
      realTriangleInequalityFromEventFlow (realTriangleInequalityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B M D W H C P N =>
      change
        some
          (RealTriangleInequalityUp.mk
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist A))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist B))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist M))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist D))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist W))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist H))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist C))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist P))
            (realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist N))) =
          some (RealTriangleInequalityUp.mk A B M D W H C P N)
      rw [realTriangleInequality_decode_encode_bhist A,
        realTriangleInequality_decode_encode_bhist B,
        realTriangleInequality_decode_encode_bhist M,
        realTriangleInequality_decode_encode_bhist D,
        realTriangleInequality_decode_encode_bhist W,
        realTriangleInequality_decode_encode_bhist H,
        realTriangleInequality_decode_encode_bhist C,
        realTriangleInequality_decode_encode_bhist P,
        realTriangleInequality_decode_encode_bhist N]

private theorem realTriangleInequalityToEventFlow_injective {x y : RealTriangleInequalityUp} :
    realTriangleInequalityToEventFlow x = realTriangleInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realTriangleInequalityFromEventFlow (realTriangleInequalityToEventFlow x) =
        realTriangleInequalityFromEventFlow (realTriangleInequalityToEventFlow y) :=
    congrArg realTriangleInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realTriangleInequality_round_trip x).symm
      (Eq.trans hread (realTriangleInequality_round_trip y)))

instance realTriangleInequalityBHistCarrier : BHistCarrier RealTriangleInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realTriangleInequalityToEventFlow
  fromEventFlow := realTriangleInequalityFromEventFlow

instance realTriangleInequalityChapterTasteGate :
    ChapterTasteGate RealTriangleInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realTriangleInequalityFromEventFlow (realTriangleInequalityToEventFlow x) = some x
    exact realTriangleInequality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realTriangleInequalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealTriangleInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realTriangleInequalityChapterTasteGate

theorem RealTriangleInequalityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realTriangleInequalityDecodeBHist (realTriangleInequalityEncodeBHist h) = h) ∧
      realTriangleInequalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.RealTriangleInequalityUp
