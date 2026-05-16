import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationResidueBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationResidueBoundaryUp : Type where
  | mk (S Sigma K T L F H C P N : BHist) : FiniteObservationResidueBoundaryUp
  deriving DecidableEq

def finiteObservationResidueBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationResidueBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationResidueBoundaryEncodeBHist h

def finiteObservationResidueBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationResidueBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationResidueBoundaryDecodeBHist tail)

private theorem finiteObservationResidueBoundary_decode_encode_bhist :
    ∀ h : BHist,
      finiteObservationResidueBoundaryDecodeBHist
        (finiteObservationResidueBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem finiteObservationResidueBoundary_mk_congr
    {S S' Sigma Sigma' K K' T T' L L' F F' H H' C C' P P' N N' : BHist}
    (hS : S' = S)
    (hSigma : Sigma' = Sigma)
    (hK : K' = K)
    (hT : T' = T)
    (hL : L' = L)
    (hF : F' = F)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    FiniteObservationResidueBoundaryUp.mk S' Sigma' K' T' L' F' H' C' P' N' =
      FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hSigma
  cases hK
  cases hT
  cases hL
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def finiteObservationResidueBoundaryFields :
    FiniteObservationResidueBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N =>
      [S, Sigma, K, T, L, F, H, C, P, N]

def finiteObservationResidueBoundaryToEventFlow :
    FiniteObservationResidueBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (finiteObservationResidueBoundaryFields x).map
        finiteObservationResidueBoundaryEncodeBHist

def finiteObservationResidueBoundaryFromEventFlow :
    EventFlow → Option FiniteObservationResidueBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | Sigma :: rest1 =>
          match rest1 with
          | [] => none
          | K :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FiniteObservationResidueBoundaryUp.mk
                                                  (finiteObservationResidueBoundaryDecodeBHist S)
                                                  (finiteObservationResidueBoundaryDecodeBHist
                                                    Sigma)
                                                  (finiteObservationResidueBoundaryDecodeBHist K)
                                                  (finiteObservationResidueBoundaryDecodeBHist T)
                                                  (finiteObservationResidueBoundaryDecodeBHist L)
                                                  (finiteObservationResidueBoundaryDecodeBHist F)
                                                  (finiteObservationResidueBoundaryDecodeBHist H)
                                                  (finiteObservationResidueBoundaryDecodeBHist C)
                                                  (finiteObservationResidueBoundaryDecodeBHist P)
                                                  (finiteObservationResidueBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem finiteObservationResidueBoundary_round_trip :
    ∀ x : FiniteObservationResidueBoundaryUp,
      finiteObservationResidueBoundaryFromEventFlow
        (finiteObservationResidueBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Sigma K T L F H C P N =>
      change
        some
          (FiniteObservationResidueBoundaryUp.mk
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist S))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist Sigma))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist K))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist T))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist L))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist F))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist H))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist C))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist P))
            (finiteObservationResidueBoundaryDecodeBHist
              (finiteObservationResidueBoundaryEncodeBHist N))) =
          some (FiniteObservationResidueBoundaryUp.mk S Sigma K T L F H C P N)
      exact
        congrArg some
          (finiteObservationResidueBoundary_mk_congr
            (finiteObservationResidueBoundary_decode_encode_bhist S)
            (finiteObservationResidueBoundary_decode_encode_bhist Sigma)
            (finiteObservationResidueBoundary_decode_encode_bhist K)
            (finiteObservationResidueBoundary_decode_encode_bhist T)
            (finiteObservationResidueBoundary_decode_encode_bhist L)
            (finiteObservationResidueBoundary_decode_encode_bhist F)
            (finiteObservationResidueBoundary_decode_encode_bhist H)
            (finiteObservationResidueBoundary_decode_encode_bhist C)
            (finiteObservationResidueBoundary_decode_encode_bhist P)
            (finiteObservationResidueBoundary_decode_encode_bhist N))

private theorem finiteObservationResidueBoundaryToEventFlow_injective
    {x y : FiniteObservationResidueBoundaryUp} :
    finiteObservationResidueBoundaryToEventFlow x =
      finiteObservationResidueBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationResidueBoundaryFromEventFlow
          (finiteObservationResidueBoundaryToEventFlow x) =
        finiteObservationResidueBoundaryFromEventFlow
          (finiteObservationResidueBoundaryToEventFlow y) :=
    congrArg finiteObservationResidueBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteObservationResidueBoundary_round_trip x).symm
      (Eq.trans hread (finiteObservationResidueBoundary_round_trip y)))

private theorem finiteObservationResidueBoundary_fields_faithful :
    ∀ x y : FiniteObservationResidueBoundaryUp,
      finiteObservationResidueBoundaryFields x =
        finiteObservationResidueBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ Sigma₁ K₁ T₁ L₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Sigma₂ K₂ T₂ L₂ F₂ H₂ C₂ P₂ N₂ =>
          simp only [finiteObservationResidueBoundaryFields] at h
          cases h
          rfl

instance finiteObservationResidueBoundaryBHistCarrier :
    BHistCarrier FiniteObservationResidueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationResidueBoundaryToEventFlow
  fromEventFlow := finiteObservationResidueBoundaryFromEventFlow

instance finiteObservationResidueBoundaryChapterTasteGate :
    ChapterTasteGate FiniteObservationResidueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationResidueBoundaryFromEventFlow
        (finiteObservationResidueBoundaryToEventFlow x) = some x
    exact finiteObservationResidueBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteObservationResidueBoundaryToEventFlow_injective heq)

instance finiteObservationResidueBoundaryFieldFaithful :
    FieldFaithful FiniteObservationResidueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteObservationResidueBoundaryFields
  field_faithful := finiteObservationResidueBoundary_fields_faithful

instance finiteObservationResidueBoundaryNontrivial :
    Nontrivial FiniteObservationResidueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationResidueBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FiniteObservationResidueBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteObservationResidueBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationResidueBoundaryChapterTasteGate

end BEDC.Derived.FiniteObservationResidueBoundaryUp
