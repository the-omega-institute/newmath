import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalNetExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalNetExtractionUp : Type where
  | mk :
      (A B epsilon D G W R E F H C P N : BHist) →
        BishopIntervalNetExtractionUp
  deriving DecidableEq

def bishopIntervalNetExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalNetExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalNetExtractionEncodeBHist h

def bishopIntervalNetExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalNetExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalNetExtractionDecodeBHist tail)

private theorem bishopIntervalNetExtractionDecode_encode_bhist :
    ∀ h : BHist,
      bishopIntervalNetExtractionDecodeBHist
        (bishopIntervalNetExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem bishopIntervalNetExtraction_mk_congr
    {A A' B B' epsilon epsilon' D D' G G' W W' R R' E E' F F' H H'
      C C' P P' N N' : BHist}
    (hA : A' = A) (hB : B' = B) (hEpsilon : epsilon' = epsilon)
    (hD : D' = D) (hG : G' = G) (hW : W' = W) (hR : R' = R)
    (hE : E' = E) (hF : F' = F) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    BishopIntervalNetExtractionUp.mk A' B' epsilon' D' G' W' R' E' F' H' C' P' N' =
      BishopIntervalNetExtractionUp.mk A B epsilon D G W R E F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hEpsilon
  cases hD
  cases hG
  cases hW
  cases hR
  cases hE
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def bishopIntervalNetExtractionToEventFlow :
    BishopIntervalNetExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalNetExtractionUp.mk A B epsilon D G W R E F H C P N =>
      [[BMark.b0],
        bishopIntervalNetExtractionEncodeBHist A,
        [BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist epsilon,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopIntervalNetExtractionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopIntervalNetExtractionEncodeBHist N]

private def bishopIntervalNetExtractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopIntervalNetExtractionEventAtDefault index rest

def bishopIntervalNetExtractionFromEventFlow (ef : EventFlow) :
    Option BishopIntervalNetExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopIntervalNetExtractionUp.mk
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 1 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 3 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 5 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 7 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 9 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 11 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 13 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 15 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 17 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 19 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 21 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 23 ef))
      (bishopIntervalNetExtractionDecodeBHist (bishopIntervalNetExtractionEventAtDefault 25 ef)))

private theorem bishopIntervalNetExtraction_round_trip :
    ∀ x : BishopIntervalNetExtractionUp,
      bishopIntervalNetExtractionFromEventFlow
        (bishopIntervalNetExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B epsilon D G W R E F H C P N =>
      change
        some
          (BishopIntervalNetExtractionUp.mk
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist A))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist B))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist epsilon))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist D))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist G))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist W))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist R))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist E))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist F))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist H))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist C))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist P))
            (bishopIntervalNetExtractionDecodeBHist
              (bishopIntervalNetExtractionEncodeBHist N))) =
          some (BishopIntervalNetExtractionUp.mk A B epsilon D G W R E F H C P N)
      exact
        congrArg some
          (bishopIntervalNetExtraction_mk_congr
            (bishopIntervalNetExtractionDecode_encode_bhist A)
            (bishopIntervalNetExtractionDecode_encode_bhist B)
            (bishopIntervalNetExtractionDecode_encode_bhist epsilon)
            (bishopIntervalNetExtractionDecode_encode_bhist D)
            (bishopIntervalNetExtractionDecode_encode_bhist G)
            (bishopIntervalNetExtractionDecode_encode_bhist W)
            (bishopIntervalNetExtractionDecode_encode_bhist R)
            (bishopIntervalNetExtractionDecode_encode_bhist E)
            (bishopIntervalNetExtractionDecode_encode_bhist F)
            (bishopIntervalNetExtractionDecode_encode_bhist H)
            (bishopIntervalNetExtractionDecode_encode_bhist C)
            (bishopIntervalNetExtractionDecode_encode_bhist P)
            (bishopIntervalNetExtractionDecode_encode_bhist N))

private theorem bishopIntervalNetExtractionToEventFlow_injective
    {x y : BishopIntervalNetExtractionUp} :
    bishopIntervalNetExtractionToEventFlow x =
      bishopIntervalNetExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalNetExtractionFromEventFlow
          (bishopIntervalNetExtractionToEventFlow x) =
        bishopIntervalNetExtractionFromEventFlow
          (bishopIntervalNetExtractionToEventFlow y) :=
    congrArg bishopIntervalNetExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopIntervalNetExtraction_round_trip x).symm
      (Eq.trans hread (bishopIntervalNetExtraction_round_trip y)))

instance bishopIntervalNetExtractionBHistCarrier :
    BHistCarrier BishopIntervalNetExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalNetExtractionToEventFlow
  fromEventFlow := bishopIntervalNetExtractionFromEventFlow

instance bishopIntervalNetExtractionChapterTasteGate :
    ChapterTasteGate BishopIntervalNetExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopIntervalNetExtractionFromEventFlow
        (bishopIntervalNetExtractionToEventFlow x) = some x
    exact bishopIntervalNetExtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopIntervalNetExtractionToEventFlow_injective heq)

theorem BishopIntervalNetExtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopIntervalNetExtractionDecodeBHist
          (bishopIntervalNetExtractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopIntervalNetExtractionUp) ∧
        Nonempty (ChapterTasteGate BishopIntervalNetExtractionUp) ∧
          bishopIntervalNetExtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopIntervalNetExtractionDecode_encode_bhist,
      ⟨bishopIntervalNetExtractionBHistCarrier⟩,
      ⟨bishopIntervalNetExtractionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.BishopIntervalNetExtractionUp
