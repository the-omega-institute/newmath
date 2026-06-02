import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteModulusCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteModulusCompactnessUp : Type where
  | mk (K E U A W H C P N : BHist) : FiniteModulusCompactnessUp
  deriving DecidableEq

def finiteModulusCompactnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteModulusCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteModulusCompactnessEncodeBHist h

def finiteModulusCompactnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteModulusCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteModulusCompactnessDecodeBHist tail)

theorem FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem finiteModulusCompactness_mk_congr
    {K K' E E' U U' A A' W W' H H' C C' P P' N N' : BHist}
    (hK : K' = K)
    (hE : E' = E)
    (hU : U' = U)
    (hA : A' = A)
    (hW : W' = W)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    FiniteModulusCompactnessUp.mk K' E' U' A' W' H' C' P' N' =
      FiniteModulusCompactnessUp.mk K E U A W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hE
  cases hU
  cases hA
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def finiteModulusCompactnessFields : FiniteModulusCompactnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteModulusCompactnessUp.mk K E U A W H C P N => [K, E, U, A, W, H, C, P, N]

def finiteModulusCompactnessToEventFlow : FiniteModulusCompactnessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteModulusCompactnessFields x).map finiteModulusCompactnessEncodeBHist

def finiteModulusCompactnessFromEventFlow : EventFlow -> Option FiniteModulusCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (FiniteModulusCompactnessUp.mk
                                              (finiteModulusCompactnessDecodeBHist K)
                                              (finiteModulusCompactnessDecodeBHist E)
                                              (finiteModulusCompactnessDecodeBHist U)
                                              (finiteModulusCompactnessDecodeBHist A)
                                              (finiteModulusCompactnessDecodeBHist W)
                                              (finiteModulusCompactnessDecodeBHist H)
                                              (finiteModulusCompactnessDecodeBHist C)
                                              (finiteModulusCompactnessDecodeBHist P)
                                              (finiteModulusCompactnessDecodeBHist N))
                                      | _ :: _ => none

private theorem finiteModulusCompactness_round_trip :
    ∀ x : FiniteModulusCompactnessUp,
      finiteModulusCompactnessFromEventFlow (finiteModulusCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K E U A W H C P N =>
      change
        some
          (FiniteModulusCompactnessUp.mk
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist K))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist E))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist U))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist A))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist W))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist H))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist C))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist P))
            (finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist N))) =
          some (FiniteModulusCompactnessUp.mk K E U A W H C P N)
      exact
        congrArg some
          (finiteModulusCompactness_mk_congr
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode K)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode E)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode U)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode A)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode W)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode H)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode C)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode P)
            (FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode N))

private theorem finiteModulusCompactnessToEventFlow_injective
    {x y : FiniteModulusCompactnessUp} :
    finiteModulusCompactnessToEventFlow x = finiteModulusCompactnessToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteModulusCompactnessFromEventFlow (finiteModulusCompactnessToEventFlow x) =
        finiteModulusCompactnessFromEventFlow (finiteModulusCompactnessToEventFlow y) :=
    congrArg finiteModulusCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteModulusCompactness_round_trip x).symm
      (Eq.trans hread (finiteModulusCompactness_round_trip y)))

private theorem finiteModulusCompactness_fields_faithful :
    ∀ x y : FiniteModulusCompactnessUp,
      finiteModulusCompactnessFields x = finiteModulusCompactnessFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 E1 U1 A1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 E2 U2 A2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteModulusCompactnessBHistCarrier : BHistCarrier FiniteModulusCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteModulusCompactnessToEventFlow
  fromEventFlow := finiteModulusCompactnessFromEventFlow

instance finiteModulusCompactnessChapterTasteGate :
    ChapterTasteGate FiniteModulusCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteModulusCompactnessFromEventFlow (finiteModulusCompactnessToEventFlow x) =
      some x
    exact finiteModulusCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteModulusCompactnessToEventFlow_injective heq)

instance finiteModulusCompactnessFieldFaithful : FieldFaithful FiniteModulusCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteModulusCompactnessFields
  field_faithful := finiteModulusCompactness_fields_faithful

instance finiteModulusCompactnessNontrivial : Nontrivial FiniteModulusCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteModulusCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteModulusCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteModulusCompactnessTasteGate_single_carrier_alignment :
    (forall h : BHist,
      finiteModulusCompactnessDecodeBHist (finiteModulusCompactnessEncodeBHist h) = h) ∧
      (forall x : FiniteModulusCompactnessUp,
        finiteModulusCompactnessFromEventFlow (finiteModulusCompactnessToEventFlow x) =
          some x) ∧
        (forall x y : FiniteModulusCompactnessUp,
          finiteModulusCompactnessToEventFlow x =
            finiteModulusCompactnessToEventFlow y -> x = y) ∧
          finiteModulusCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FiniteModulusCompactnessTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact finiteModulusCompactness_round_trip
    · constructor
      · intro x y heq
        exact finiteModulusCompactnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteModulusCompactnessUp
