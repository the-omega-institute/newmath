import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RieszSpaceUp : Type where
  | mk (V L N P H C S : BHist) : RieszSpaceUp
  deriving DecidableEq

def rieszSpaceUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszSpaceUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszSpaceUpEncodeBHist h

def rieszSpaceUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszSpaceUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszSpaceUpDecodeBHist tail)

private theorem RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    rieszSpaceUpEncodeBHist h = rieszSpaceUpEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist h) =
        rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist k) :=
    congrArg rieszSpaceUpDecodeBHist heq
  exact
    Eq.trans (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode h).symm
      (Eq.trans hdecode
        (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode k))

private theorem RieszSpaceUpTasteGate_single_carrier_alignment_mk_congr
    {V V' L L' N N' P P' H H' C C' S S' : BHist}
    (hV : V' = V)
    (hL : L' = L)
    (hN : N' = N)
    (hP : P' = P)
    (hH : H' = H)
    (hC : C' = C)
    (hS : S' = S) :
    RieszSpaceUp.mk V' L' N' P' H' C' S' =
      RieszSpaceUp.mk V L N P H C S := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hV
  cases hL
  cases hN
  cases hP
  cases hH
  cases hC
  cases hS
  rfl

def rieszSpaceUpFields : RieszSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszSpaceUp.mk V L N P H C S => [V, L, N, P, H, C, S]

def rieszSpaceUpToEventFlow : RieszSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rieszSpaceUpFields x).map rieszSpaceUpEncodeBHist

def rieszSpaceUpFromEventFlow : EventFlow → Option RieszSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | V :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | N :: rest2 =>
              match rest2 with
              | [] => none
              | P :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | S :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (RieszSpaceUp.mk
                                      (rieszSpaceUpDecodeBHist V)
                                      (rieszSpaceUpDecodeBHist L)
                                      (rieszSpaceUpDecodeBHist N)
                                      (rieszSpaceUpDecodeBHist P)
                                      (rieszSpaceUpDecodeBHist H)
                                      (rieszSpaceUpDecodeBHist C)
                                      (rieszSpaceUpDecodeBHist S))
                              | _ :: _ => none

private theorem RieszSpaceUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RieszSpaceUp,
      rieszSpaceUpFromEventFlow (rieszSpaceUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V L N P H C S =>
      change
        some
          (RieszSpaceUp.mk
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist V))
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist L))
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist N))
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist P))
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist H))
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist C))
            (rieszSpaceUpDecodeBHist (rieszSpaceUpEncodeBHist S))) =
          some (RieszSpaceUp.mk V L N P H C S)
      exact
        congrArg some
          (RieszSpaceUpTasteGate_single_carrier_alignment_mk_congr
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode V)
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode L)
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode N)
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode P)
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode H)
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode C)
            (RieszSpaceUpTasteGate_single_carrier_alignment_decode_encode S))

private theorem RieszSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RieszSpaceUp} :
    rieszSpaceUpToEventFlow x = rieszSpaceUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk V₁ L₁ N₁ P₁ H₁ C₁ S₁ =>
      cases y with
      | mk V₂ L₂ N₂ P₂ H₂ C₂ S₂ =>
          injection heq with hV t0
          injection t0 with hL t1
          injection t1 with hN t2
          injection t2 with hP t3
          injection t3 with hH t4
          injection t4 with hC t5
          injection t5 with hS _
          have eV :
              V₁ = V₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hV
          have eL :
              L₁ = L₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hL
          have eN :
              N₁ = N₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hN
          have eP :
              P₁ = P₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hP
          have eH :
              H₁ = H₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hH
          have eC :
              C₁ = C₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hC
          have eS :
              S₁ = S₂ :=
            RieszSpaceUpTasteGate_single_carrier_alignment_encode_injective hS
          cases eV
          cases eL
          cases eN
          cases eP
          cases eH
          cases eC
          cases eS
          rfl

private theorem RieszSpaceUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RieszSpaceUp, rieszSpaceUpFields x = rieszSpaceUpFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V₁ L₁ N₁ P₁ H₁ C₁ S₁ =>
      cases y with
      | mk V₂ L₂ N₂ P₂ H₂ C₂ S₂ =>
          cases hfields
          rfl

instance rieszSpaceUpBHistCarrier : BHistCarrier RieszSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszSpaceUpToEventFlow
  fromEventFlow := rieszSpaceUpFromEventFlow

instance rieszSpaceUpChapterTasteGate : ChapterTasteGate RieszSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rieszSpaceUpFromEventFlow (rieszSpaceUpToEventFlow x) = some x
    exact RieszSpaceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RieszSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rieszSpaceUpFieldFaithful : FieldFaithful RieszSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rieszSpaceUpFields
  field_faithful := RieszSpaceUpTasteGate_single_carrier_alignment_fields_faithful

instance rieszSpaceUpNontrivial : Nontrivial RieszSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RieszSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RieszSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RieszSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rieszSpaceUpChapterTasteGate

theorem RieszSpaceUpTasteGate_single_carrier_alignment :
    (forall x : RieszSpaceUp,
      rieszSpaceUpFromEventFlow (rieszSpaceUpToEventFlow x) = some x) ∧
      (forall x y : RieszSpaceUp,
        rieszSpaceUpToEventFlow x = rieszSpaceUpToEventFlow y → x = y) ∧
        rieszSpaceUpFields
          (RieszSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RieszSpaceUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => RieszSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RieszSpaceUp
