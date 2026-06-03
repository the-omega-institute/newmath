import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AffineContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AffineContractionUp : Type where
  | mk (X d V add zero L b T G lambda M H C P N : BHist) : AffineContractionUp
  deriving DecidableEq

def affineContractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: affineContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: affineContractionEncodeBHist h

def affineContractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (affineContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (affineContractionDecodeBHist tail)

private def affineContractionNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => affineContractionNthRawEvent tail n

private theorem affineContraction_decode_encode_bhist :
    ∀ h : BHist, affineContractionDecodeBHist (affineContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem affineContraction_mk_congr
    {X X' d d' V V' add add' zero zero' L L' b b' T T' G G' lambda lambda'
      M M' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hd : d' = d) (hV : V' = V) (hAdd : add' = add)
    (hZero : zero' = zero) (hL : L' = L) (hb : b' = b) (hT : T' = T)
    (hG : G' = G) (hLambda : lambda' = lambda) (hM : M' = M) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    AffineContractionUp.mk X' d' V' add' zero' L' b' T' G' lambda' M' H' C' P' N' =
      AffineContractionUp.mk X d V add zero L b T G lambda M H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hd
  cases hV
  cases hAdd
  cases hZero
  cases hL
  cases hb
  cases hT
  cases hG
  cases hLambda
  cases hM
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def affineContractionFields : AffineContractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AffineContractionUp.mk X d V add zero L b T G lambda M H C P N =>
      [X, d, V, add, zero, L, b, T, G, lambda, M, H, C, P, N]

def affineContractionToEventFlow : AffineContractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AffineContractionUp.mk X d V add zero L b T G lambda M H C P N =>
      [affineContractionEncodeBHist X,
        affineContractionEncodeBHist d,
        affineContractionEncodeBHist V,
        affineContractionEncodeBHist add,
        affineContractionEncodeBHist zero,
        affineContractionEncodeBHist L,
        affineContractionEncodeBHist b,
        affineContractionEncodeBHist T,
        affineContractionEncodeBHist G,
        affineContractionEncodeBHist lambda,
        affineContractionEncodeBHist M,
        affineContractionEncodeBHist H,
        affineContractionEncodeBHist C,
        affineContractionEncodeBHist P,
        affineContractionEncodeBHist N]

def affineContractionFromEventFlow (ef : EventFlow) : Option AffineContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AffineContractionUp.mk
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 0))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 1))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 2))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 3))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 4))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 5))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 6))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 7))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 8))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 9))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 10))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 11))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 12))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 13))
      (affineContractionDecodeBHist (affineContractionNthRawEvent ef 14)))

private theorem affineContraction_round_trip :
    ∀ x : AffineContractionUp,
      affineContractionFromEventFlow (affineContractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d V add zero L b T G lambda M H C P N =>
      exact
        congrArg some
          (affineContraction_mk_congr
            (affineContraction_decode_encode_bhist X)
            (affineContraction_decode_encode_bhist d)
            (affineContraction_decode_encode_bhist V)
            (affineContraction_decode_encode_bhist add)
            (affineContraction_decode_encode_bhist zero)
            (affineContraction_decode_encode_bhist L)
            (affineContraction_decode_encode_bhist b)
            (affineContraction_decode_encode_bhist T)
            (affineContraction_decode_encode_bhist G)
            (affineContraction_decode_encode_bhist lambda)
            (affineContraction_decode_encode_bhist M)
            (affineContraction_decode_encode_bhist H)
            (affineContraction_decode_encode_bhist C)
            (affineContraction_decode_encode_bhist P)
            (affineContraction_decode_encode_bhist N))

private theorem affineContractionToEventFlow_injective {x y : AffineContractionUp} :
    affineContractionToEventFlow x = affineContractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      affineContractionFromEventFlow (affineContractionToEventFlow x) =
        affineContractionFromEventFlow (affineContractionToEventFlow y) :=
    congrArg affineContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (affineContraction_round_trip x).symm
      (Eq.trans hread (affineContraction_round_trip y)))

private theorem affineContraction_field_faithful :
    ∀ x y : AffineContractionUp, affineContractionFields x = affineContractionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X d V add zero L b T G lambda M H C P N =>
      cases y with
      | mk X' d' V' add' zero' L' b' T' G' lambda' M' H' C' P' N' =>
          cases hfields
          rfl

instance affineContractionBHistCarrier : BHistCarrier AffineContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := affineContractionToEventFlow
  fromEventFlow := affineContractionFromEventFlow

instance affineContractionChapterTasteGate :
    ChapterTasteGate AffineContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change affineContractionFromEventFlow (affineContractionToEventFlow x) = some x
    exact affineContraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (affineContractionToEventFlow_injective heq)

instance affineContractionFieldFaithful : FieldFaithful AffineContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := affineContractionFields
  field_faithful := affineContraction_field_faithful

instance affineContractionNontrivial : Nontrivial AffineContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AffineContractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AffineContractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AffineContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  affineContractionChapterTasteGate

theorem AffineContractionTasteGate_single_carrier_alignment :
    (∀ h : BHist, affineContractionDecodeBHist (affineContractionEncodeBHist h) = h) ∧
      (∀ x : AffineContractionUp,
        affineContractionFromEventFlow (affineContractionToEventFlow x) = some x) ∧
        (∀ x y : AffineContractionUp,
          affineContractionToEventFlow x = affineContractionToEventFlow y -> x = y) ∧
          affineContractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨affineContraction_decode_encode_bhist,
      affineContraction_round_trip,
      (fun _ _ heq => affineContractionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AffineContractionUp
