import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KreinMilmanFiniteExtremeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KreinMilmanFiniteExtremeUp : Type where
  | mk (M V X F E S W H C P N : BHist) : KreinMilmanFiniteExtremeUp
  deriving DecidableEq

def kreinMilmanFiniteExtremeUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kreinMilmanFiniteExtremeUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kreinMilmanFiniteExtremeUpEncodeBHist h

def kreinMilmanFiniteExtremeUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kreinMilmanFiniteExtremeUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kreinMilmanFiniteExtremeUpDecodeBHist tail)

private theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      kreinMilmanFiniteExtremeUpDecodeBHist
        (kreinMilmanFiniteExtremeUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    kreinMilmanFiniteExtremeUpEncodeBHist h =
      kreinMilmanFiniteExtremeUpEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      kreinMilmanFiniteExtremeUpDecodeBHist
          (kreinMilmanFiniteExtremeUpEncodeBHist h) =
        kreinMilmanFiniteExtremeUpDecodeBHist
          (kreinMilmanFiniteExtremeUpEncodeBHist k) :=
    congrArg kreinMilmanFiniteExtremeUpDecodeBHist heq
  exact
    Eq.trans
      (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode h).symm
      (Eq.trans hdecode
        (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode k))

private theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_mk_congr
    {M M' V V' X X' F F' E E' S S' W W' H H' C C' P P' N N' : BHist}
    (hM : M' = M)
    (hV : V' = V)
    (hX : X' = X)
    (hF : F' = F)
    (hE : E' = E)
    (hS : S' = S)
    (hW : W' = W)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    KreinMilmanFiniteExtremeUp.mk M' V' X' F' E' S' W' H' C' P' N' =
      KreinMilmanFiniteExtremeUp.mk M V X F E S W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hV
  cases hX
  cases hF
  cases hE
  cases hS
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def kreinMilmanFiniteExtremeUpFields :
    KreinMilmanFiniteExtremeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KreinMilmanFiniteExtremeUp.mk M V X F E S W H C P N =>
      [M, V, X, F, E, S, W, H, C, P, N]

def kreinMilmanFiniteExtremeUpToEventFlow :
    KreinMilmanFiniteExtremeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kreinMilmanFiniteExtremeUpFields x).map kreinMilmanFiniteExtremeUpEncodeBHist

def kreinMilmanFiniteExtremeUpFromEventFlow :
    EventFlow → Option KreinMilmanFiniteExtremeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | V :: rest1 =>
          match rest1 with
          | [] => none
          | X :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | W :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (KreinMilmanFiniteExtremeUp.mk
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist M)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist V)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist X)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist F)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist E)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist S)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist W)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist H)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist C)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist P)
                                                      (kreinMilmanFiniteExtremeUpDecodeBHist N))
                                              | _ :: _ => none

private theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KreinMilmanFiniteExtremeUp,
      kreinMilmanFiniteExtremeUpFromEventFlow
        (kreinMilmanFiniteExtremeUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M V X F E S W H C P N =>
      change
        some
          (KreinMilmanFiniteExtremeUp.mk
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist M))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist V))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist X))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist F))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist E))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist S))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist W))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist H))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist C))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist P))
            (kreinMilmanFiniteExtremeUpDecodeBHist
              (kreinMilmanFiniteExtremeUpEncodeBHist N))) =
          some (KreinMilmanFiniteExtremeUp.mk M V X F E S W H C P N)
      exact
        congrArg some
          (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_mk_congr
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode M)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode V)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode X)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode F)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode E)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode S)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode W)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode H)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode C)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode P)
            (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_decode_encode N))

private theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KreinMilmanFiniteExtremeUp} :
    kreinMilmanFiniteExtremeUpToEventFlow x =
      kreinMilmanFiniteExtremeUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk M₁ V₁ X₁ F₁ E₁ S₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ V₂ X₂ F₂ E₂ S₂ W₂ H₂ C₂ P₂ N₂ =>
          injection heq with hM t0
          injection t0 with hV t1
          injection t1 with hX t2
          injection t2 with hF t3
          injection t3 with hE t4
          injection t4 with hS t5
          injection t5 with hW t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          have eM :
              M₁ = M₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hM
          have eV :
              V₁ = V₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hV
          have eX :
              X₁ = X₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hX
          have eF :
              F₁ = F₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hF
          have eE :
              E₁ = E₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hE
          have eS :
              S₁ = S₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hS
          have eW :
              W₁ = W₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hW
          have eH :
              H₁ = H₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hH
          have eC :
              C₁ = C₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hC
          have eP :
              P₁ = P₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hP
          have eN :
              N₁ = N₂ :=
            KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_encode_injective hN
          cases eM
          cases eV
          cases eX
          cases eF
          cases eE
          cases eS
          cases eW
          cases eH
          cases eC
          cases eP
          cases eN
          rfl

private theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : KreinMilmanFiniteExtremeUp,
      kreinMilmanFiniteExtremeUpFields x =
        kreinMilmanFiniteExtremeUpFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ V₁ X₁ F₁ E₁ S₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ V₂ X₂ F₂ E₂ S₂ W₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance kreinMilmanFiniteExtremeUpBHistCarrier :
    BHistCarrier KreinMilmanFiniteExtremeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kreinMilmanFiniteExtremeUpToEventFlow
  fromEventFlow := kreinMilmanFiniteExtremeUpFromEventFlow

instance kreinMilmanFiniteExtremeUpChapterTasteGate :
    ChapterTasteGate KreinMilmanFiniteExtremeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kreinMilmanFiniteExtremeUpFromEventFlow
        (kreinMilmanFiniteExtremeUpToEventFlow x) = some x
    exact KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance kreinMilmanFiniteExtremeUpFieldFaithful :
    FieldFaithful KreinMilmanFiniteExtremeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kreinMilmanFiniteExtremeUpFields
  field_faithful :=
    KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_fields_faithful

instance kreinMilmanFiniteExtremeUpNontrivial :
    Nontrivial KreinMilmanFiniteExtremeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KreinMilmanFiniteExtremeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KreinMilmanFiniteExtremeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KreinMilmanFiniteExtremeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kreinMilmanFiniteExtremeUpChapterTasteGate

theorem KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment :
    (forall x : KreinMilmanFiniteExtremeUp,
      kreinMilmanFiniteExtremeUpFromEventFlow
        (kreinMilmanFiniteExtremeUpToEventFlow x) = some x) ∧
      (forall x y : KreinMilmanFiniteExtremeUp,
        kreinMilmanFiniteExtremeUpToEventFlow x =
          kreinMilmanFiniteExtremeUpToEventFlow y → x = y) ∧
        kreinMilmanFiniteExtremeUpFields
          (KreinMilmanFiniteExtremeUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        KreinMilmanFiniteExtremeUpTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.KreinMilmanFiniteExtremeUp
