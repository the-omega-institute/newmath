import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceProductStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceProductStabilityUp : Type where
  | mk (A B WA WB D P K R E H C L N : BHist) :
      CauchySequenceProductStabilityUp
  deriving DecidableEq

def cauchySequenceProductStabilityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceProductStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceProductStabilityEncodeBHist h

def cauchySequenceProductStabilityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceProductStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceProductStabilityDecodeBHist tail)

private theorem cauchySequenceProductStabilityDecode_encode_bhist :
    forall h : BHist,
      cauchySequenceProductStabilityDecodeBHist
        (cauchySequenceProductStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceProductStabilityFields :
    CauchySequenceProductStabilityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceProductStabilityUp.mk A B WA WB D P K R E H C L N =>
      [A, B, WA, WB, D, P, K, R, E, H, C, L, N]

def cauchySequenceProductStabilityToEventFlow :
    CauchySequenceProductStabilityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchySequenceProductStabilityFields x).map
        cauchySequenceProductStabilityEncodeBHist

def cauchySequenceProductStabilityFromEventFlow :
    EventFlow -> Option CauchySequenceProductStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _A :: [] => none
  | _A :: _B :: [] => none
  | _A :: _B :: _WA :: [] => none
  | _A :: _B :: _WA :: _WB :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: _R :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: _R :: _E :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: _R :: _E :: _H :: [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: _R :: _E :: _H :: _C ::
      [] => none
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: _R :: _E :: _H :: _C ::
      _L :: [] => none
  | A :: B :: WA :: WB :: D :: P :: K :: R :: E :: H :: C :: L :: N :: [] =>
      some
        (CauchySequenceProductStabilityUp.mk
          (cauchySequenceProductStabilityDecodeBHist A)
          (cauchySequenceProductStabilityDecodeBHist B)
          (cauchySequenceProductStabilityDecodeBHist WA)
          (cauchySequenceProductStabilityDecodeBHist WB)
          (cauchySequenceProductStabilityDecodeBHist D)
          (cauchySequenceProductStabilityDecodeBHist P)
          (cauchySequenceProductStabilityDecodeBHist K)
          (cauchySequenceProductStabilityDecodeBHist R)
          (cauchySequenceProductStabilityDecodeBHist E)
          (cauchySequenceProductStabilityDecodeBHist H)
          (cauchySequenceProductStabilityDecodeBHist C)
          (cauchySequenceProductStabilityDecodeBHist L)
          (cauchySequenceProductStabilityDecodeBHist N))
  | _A :: _B :: _WA :: _WB :: _D :: _P :: _K :: _R :: _E :: _H :: _C ::
      _L :: _N :: _extra :: _rest => none

private theorem cauchySequenceProductStability_round_trip :
    forall x : CauchySequenceProductStabilityUp,
      cauchySequenceProductStabilityFromEventFlow
        (cauchySequenceProductStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB D P K R E H C L N =>
      change
        some
            (CauchySequenceProductStabilityUp.mk
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist A))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist B))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist WA))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist WB))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist D))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist P))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist K))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist R))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist E))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist H))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist C))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist L))
              (cauchySequenceProductStabilityDecodeBHist
                (cauchySequenceProductStabilityEncodeBHist N))) =
          some (CauchySequenceProductStabilityUp.mk A B WA WB D P K R E H C L N)
      rw [cauchySequenceProductStabilityDecode_encode_bhist A,
        cauchySequenceProductStabilityDecode_encode_bhist B,
        cauchySequenceProductStabilityDecode_encode_bhist WA,
        cauchySequenceProductStabilityDecode_encode_bhist WB,
        cauchySequenceProductStabilityDecode_encode_bhist D,
        cauchySequenceProductStabilityDecode_encode_bhist P,
        cauchySequenceProductStabilityDecode_encode_bhist K,
        cauchySequenceProductStabilityDecode_encode_bhist R,
        cauchySequenceProductStabilityDecode_encode_bhist E,
        cauchySequenceProductStabilityDecode_encode_bhist H,
        cauchySequenceProductStabilityDecode_encode_bhist C,
        cauchySequenceProductStabilityDecode_encode_bhist L,
        cauchySequenceProductStabilityDecode_encode_bhist N]

private theorem cauchySequenceProductStabilityToEventFlow_injective
    {x y : CauchySequenceProductStabilityUp} :
    cauchySequenceProductStabilityToEventFlow x =
      cauchySequenceProductStabilityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceProductStabilityFromEventFlow
          (cauchySequenceProductStabilityToEventFlow x) =
        cauchySequenceProductStabilityFromEventFlow
          (cauchySequenceProductStabilityToEventFlow y) :=
    congrArg cauchySequenceProductStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceProductStability_round_trip x).symm
      (Eq.trans hread (cauchySequenceProductStability_round_trip y)))

instance cauchySequenceProductStabilityBHistCarrier :
    BHistCarrier CauchySequenceProductStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceProductStabilityToEventFlow
  fromEventFlow := cauchySequenceProductStabilityFromEventFlow

instance cauchySequenceProductStabilityChapterTasteGate :
    ChapterTasteGate CauchySequenceProductStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceProductStabilityFromEventFlow
        (cauchySequenceProductStabilityToEventFlow x) = some x
    exact cauchySequenceProductStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceProductStabilityToEventFlow_injective heq)

instance cauchySequenceProductStabilityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchySequenceProductStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySequenceProductStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySequenceProductStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySequenceProductStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceProductStabilityChapterTasteGate

theorem CauchySequenceProductStabilityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchySequenceProductStabilityDecodeBHist
        (cauchySequenceProductStabilityEncodeBHist h) = h) ∧
      (forall x : CauchySequenceProductStabilityUp,
        cauchySequenceProductStabilityFromEventFlow
          (cauchySequenceProductStabilityToEventFlow x) = some x) ∧
        (forall x y : CauchySequenceProductStabilityUp,
          cauchySequenceProductStabilityToEventFlow x =
            cauchySequenceProductStabilityToEventFlow y -> x = y) ∧
          cauchySequenceProductStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchySequenceProductStabilityDecode_encode_bhist,
      cauchySequenceProductStability_round_trip,
      (fun _ _ heq => cauchySequenceProductStabilityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySequenceProductStabilityUp
