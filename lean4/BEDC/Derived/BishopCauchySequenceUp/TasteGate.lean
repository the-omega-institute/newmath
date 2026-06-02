import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchySequenceUp : Type where
  | mk (S D X U R H C P N : BHist) : BishopCauchySequenceUp
  deriving DecidableEq

def bishopCauchySequenceUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchySequenceUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchySequenceUpEncodeBHist h

def bishopCauchySequenceUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchySequenceUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchySequenceUpDecodeBHist tail)

private theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopCauchySequenceUpDecodeBHist
        (bishopCauchySequenceUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    bishopCauchySequenceUpEncodeBHist h =
      bishopCauchySequenceUpEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      bishopCauchySequenceUpDecodeBHist
          (bishopCauchySequenceUpEncodeBHist h) =
        bishopCauchySequenceUpDecodeBHist
          (bishopCauchySequenceUpEncodeBHist k) :=
    congrArg bishopCauchySequenceUpDecodeBHist heq
  exact
    Eq.trans
      (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode h).symm
      (Eq.trans hdecode
        (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode k))

private theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment_mk_congr
    {S S' D D' X X' U U' R R' H H' C C' P P' N N' : BHist}
    (hS : S' = S)
    (hD : D' = D)
    (hX : X' = X)
    (hU : U' = U)
    (hR : R' = R)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    BishopCauchySequenceUp.mk S' D' X' U' R' H' C' P' N' =
      BishopCauchySequenceUp.mk S D X U R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hD
  cases hX
  cases hU
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def bishopCauchySequenceUpFields :
    BishopCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchySequenceUp.mk S D X U R H C P N => [S, D, X, U, R, H, C, P, N]

def bishopCauchySequenceUpToEventFlow :
    BishopCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCauchySequenceUpFields x).map bishopCauchySequenceUpEncodeBHist

def bishopCauchySequenceUpFromEventFlow :
    EventFlow → Option BishopCauchySequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | X :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
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
                                            (BishopCauchySequenceUp.mk
                                              (bishopCauchySequenceUpDecodeBHist S)
                                              (bishopCauchySequenceUpDecodeBHist D)
                                              (bishopCauchySequenceUpDecodeBHist X)
                                              (bishopCauchySequenceUpDecodeBHist U)
                                              (bishopCauchySequenceUpDecodeBHist R)
                                              (bishopCauchySequenceUpDecodeBHist H)
                                              (bishopCauchySequenceUpDecodeBHist C)
                                              (bishopCauchySequenceUpDecodeBHist P)
                                              (bishopCauchySequenceUpDecodeBHist N))
                                      | _ :: _ => none

private theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCauchySequenceUp,
      bishopCauchySequenceUpFromEventFlow
        (bishopCauchySequenceUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D X U R H C P N =>
      change
        some
          (BishopCauchySequenceUp.mk
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist S))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist D))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist X))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist U))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist R))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist H))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist C))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist P))
            (bishopCauchySequenceUpDecodeBHist
              (bishopCauchySequenceUpEncodeBHist N))) =
          some (BishopCauchySequenceUp.mk S D X U R H C P N)
      exact
        congrArg some
          (BishopCauchySequenceUpTasteGate_single_carrier_alignment_mk_congr
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode S)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode D)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode X)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode U)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode R)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode H)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode C)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode P)
            (BishopCauchySequenceUpTasteGate_single_carrier_alignment_decode_encode N))

private theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchySequenceUp} :
    bishopCauchySequenceUpToEventFlow x =
      bishopCauchySequenceUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ D₁ X₁ U₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ D₂ X₂ U₂ R₂ H₂ C₂ P₂ N₂ =>
          injection heq with hS t0
          injection t0 with hD t1
          injection t1 with hX t2
          injection t2 with hU t3
          injection t3 with hR t4
          injection t4 with hH t5
          injection t5 with hC t6
          injection t6 with hP t7
          injection t7 with hN _
          have eS :
              S₁ = S₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hS
          have eD :
              D₁ = D₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hD
          have eX :
              X₁ = X₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hX
          have eU :
              U₁ = U₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hU
          have eR :
              R₁ = R₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hR
          have eH :
              H₁ = H₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hH
          have eC :
              C₁ = C₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hC
          have eP :
              P₁ = P₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hP
          have eN :
              N₁ = N₂ :=
            BishopCauchySequenceUpTasteGate_single_carrier_alignment_encode_injective hN
          cases eS
          cases eD
          cases eX
          cases eU
          cases eR
          cases eH
          cases eC
          cases eP
          cases eN
          rfl

private theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopCauchySequenceUp,
      bishopCauchySequenceUpFields x =
        bishopCauchySequenceUpFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ D₁ X₁ U₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ D₂ X₂ U₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopCauchySequenceUpBHistCarrier :
    BHistCarrier BishopCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchySequenceUpToEventFlow
  fromEventFlow := bishopCauchySequenceUpFromEventFlow

instance bishopCauchySequenceUpChapterTasteGate :
    ChapterTasteGate BishopCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchySequenceUpFromEventFlow
        (bishopCauchySequenceUpToEventFlow x) = some x
    exact BishopCauchySequenceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchySequenceUpTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance bishopCauchySequenceUpFieldFaithful :
    FieldFaithful BishopCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCauchySequenceUpFields
  field_faithful :=
    BishopCauchySequenceUpTasteGate_single_carrier_alignment_fields_faithful

instance bishopCauchySequenceUpNontrivial :
    Nontrivial BishopCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCauchySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCauchySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchySequenceUpChapterTasteGate

theorem BishopCauchySequenceUpTasteGate_single_carrier_alignment :
    (forall x : BishopCauchySequenceUp,
      bishopCauchySequenceUpFromEventFlow
        (bishopCauchySequenceUpToEventFlow x) = some x) ∧
      (forall x y : BishopCauchySequenceUp,
        bishopCauchySequenceUpToEventFlow x =
          bishopCauchySequenceUpToEventFlow y → x = y) ∧
        bishopCauchySequenceUpFields
          (BishopCauchySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨BishopCauchySequenceUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        BishopCauchySequenceUpTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.BishopCauchySequenceUp
