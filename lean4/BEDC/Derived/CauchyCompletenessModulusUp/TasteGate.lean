import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletenessModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletenessModulusUp : Type where
  | mk (R M D S B L H C P N : BHist) : CauchyCompletenessModulusUp
  deriving DecidableEq

def cauchyCompletenessModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletenessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletenessModulusEncodeBHist h

def cauchyCompletenessModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletenessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletenessModulusDecodeBHist tail)

private theorem CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletenessModulusDecodeBHist (cauchyCompletenessModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletenessModulusFields : CauchyCompletenessModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletenessModulusUp.mk R M D S B L H C P N =>
      [R, M, D, S, B, L, H, C, P, N]

def cauchyCompletenessModulusToEventFlow :
    CauchyCompletenessModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletenessModulusFields x).map
        cauchyCompletenessModulusEncodeBHist

def cauchyCompletenessModulusFromEventFlow :
    EventFlow → Option CauchyCompletenessModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: restR =>
      match restR with
      | M :: restM =>
          match restM with
          | D :: restD =>
              match restD with
              | S :: restS =>
                  match restS with
                  | B :: restB =>
                      match restB with
                      | L :: restL =>
                          match restL with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchyCompletenessModulusUp.mk
                                                  (cauchyCompletenessModulusDecodeBHist R)
                                                  (cauchyCompletenessModulusDecodeBHist M)
                                                  (cauchyCompletenessModulusDecodeBHist D)
                                                  (cauchyCompletenessModulusDecodeBHist S)
                                                  (cauchyCompletenessModulusDecodeBHist B)
                                                  (cauchyCompletenessModulusDecodeBHist L)
                                                  (cauchyCompletenessModulusDecodeBHist H)
                                                  (cauchyCompletenessModulusDecodeBHist C)
                                                  (cauchyCompletenessModulusDecodeBHist P)
                                                  (cauchyCompletenessModulusDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyCompletenessModulus_mk_congr
    {R R' M M' D D' S S' B B' L L' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hM : M' = M) (hD : D' = D) (hS : S' = S)
    (hB : B' = B) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyCompletenessModulusUp.mk R' M' D' S' B' L' H' C' P' N' =
      CauchyCompletenessModulusUp.mk R M D S B L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hM
  cases hD
  cases hS
  cases hB
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyCompletenessModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletenessModulusUp,
      cauchyCompletenessModulusFromEventFlow
        (cauchyCompletenessModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M D S B L H C P N =>
      exact
        congrArg some
          (cauchyCompletenessModulus_mk_congr
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode R)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode M)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode D)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode S)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode B)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode L)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode H)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode C)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode P)
            (CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode N))

private theorem cauchyCompletenessModulusToEventFlow_injective
    {x y : CauchyCompletenessModulusUp} :
    cauchyCompletenessModulusToEventFlow x =
      cauchyCompletenessModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletenessModulusFromEventFlow
          (cauchyCompletenessModulusToEventFlow x) =
        cauchyCompletenessModulusFromEventFlow
          (cauchyCompletenessModulusToEventFlow y) :=
    congrArg cauchyCompletenessModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletenessModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletenessModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyCompletenessModulus_field_faithful :
    ∀ x y : CauchyCompletenessModulusUp,
      cauchyCompletenessModulusFields x = cauchyCompletenessModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R M D S B L H C P N =>
      cases y with
      | mk R' M' D' S' B' L' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyCompletenessModulusBHistCarrier :
    BHistCarrier CauchyCompletenessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletenessModulusToEventFlow
  fromEventFlow := cauchyCompletenessModulusFromEventFlow

instance cauchyCompletenessModulusChapterTasteGate :
    ChapterTasteGate CauchyCompletenessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletenessModulusFromEventFlow
          (cauchyCompletenessModulusToEventFlow x) = some x
    exact CauchyCompletenessModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletenessModulusToEventFlow_injective heq)

instance cauchyCompletenessModulusFieldFaithful :
    FieldFaithful CauchyCompletenessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletenessModulusFields
  field_faithful := cauchyCompletenessModulus_field_faithful

instance cauchyCompletenessModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletenessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletenessModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletenessModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletenessModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletenessModulusChapterTasteGate

theorem CauchyCompletenessModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletenessModulusUp) ∧
      Nonempty (FieldFaithful CauchyCompletenessModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletenessModulusUp) ∧
      (∀ h : BHist,
        cauchyCompletenessModulusDecodeBHist
          (cauchyCompletenessModulusEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletenessModulusUp,
        cauchyCompletenessModulusFromEventFlow
          (cauchyCompletenessModulusToEventFlow x) = some x) ∧
      (∀ x y : CauchyCompletenessModulusUp,
        cauchyCompletenessModulusToEventFlow x =
          cauchyCompletenessModulusToEventFlow y → x = y) ∧
      cauchyCompletenessModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyCompletenessModulusChapterTasteGate⟩
  constructor
  · exact ⟨cauchyCompletenessModulusFieldFaithful⟩
  constructor
  · exact ⟨cauchyCompletenessModulusNontrivial⟩
  constructor
  · exact CauchyCompletenessModulusTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyCompletenessModulusTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyCompletenessModulusToEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyCompletenessModulusUp
