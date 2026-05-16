import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedOpenFitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedOpenFitUp : Type where
  | mk : (H Pi O M F Q L R N : BHist) → RealityConstrainedOpenFitUp
  deriving DecidableEq

def realityConstrainedOpenFitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedOpenFitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedOpenFitEncodeBHist h

def realityConstrainedOpenFitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedOpenFitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedOpenFitDecodeBHist tail)

private theorem realityConstrainedOpenFit_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedOpenFitDecodeBHist (realityConstrainedOpenFitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedOpenFitFields : RealityConstrainedOpenFitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedOpenFitUp.mk H Pi O M F Q L R N => [H, Pi, O, M, F, Q, L, R, N]

def realityConstrainedOpenFitToEventFlow : RealityConstrainedOpenFitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realityConstrainedOpenFitFields x).map realityConstrainedOpenFitEncodeBHist

def realityConstrainedOpenFitFromEventFlow :
    EventFlow → Option RealityConstrainedOpenFitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | H :: rest0 =>
      match rest0 with
      | [] => none
      | Pi :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | L :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RealityConstrainedOpenFitUp.mk
                                              (realityConstrainedOpenFitDecodeBHist H)
                                              (realityConstrainedOpenFitDecodeBHist Pi)
                                              (realityConstrainedOpenFitDecodeBHist O)
                                              (realityConstrainedOpenFitDecodeBHist M)
                                              (realityConstrainedOpenFitDecodeBHist F)
                                              (realityConstrainedOpenFitDecodeBHist Q)
                                              (realityConstrainedOpenFitDecodeBHist L)
                                              (realityConstrainedOpenFitDecodeBHist R)
                                              (realityConstrainedOpenFitDecodeBHist N))
                                      | _ :: _ => none

private theorem realityConstrainedOpenFit_round_trip :
    ∀ x : RealityConstrainedOpenFitUp,
      realityConstrainedOpenFitFromEventFlow
        (realityConstrainedOpenFitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H Pi O M F Q L R N =>
      change
        some
          (RealityConstrainedOpenFitUp.mk
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist H))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist Pi))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist O))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist M))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist F))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist Q))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist L))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist R))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist N))) =
          some (RealityConstrainedOpenFitUp.mk H Pi O M F Q L R N)
      rw [realityConstrainedOpenFit_decode_encode_bhist H,
        realityConstrainedOpenFit_decode_encode_bhist Pi,
        realityConstrainedOpenFit_decode_encode_bhist O,
        realityConstrainedOpenFit_decode_encode_bhist M,
        realityConstrainedOpenFit_decode_encode_bhist F,
        realityConstrainedOpenFit_decode_encode_bhist Q,
        realityConstrainedOpenFit_decode_encode_bhist L,
        realityConstrainedOpenFit_decode_encode_bhist R,
        realityConstrainedOpenFit_decode_encode_bhist N]

private theorem realityConstrainedOpenFitToEventFlow_injective
    {x y : RealityConstrainedOpenFitUp} :
    realityConstrainedOpenFitToEventFlow x =
      realityConstrainedOpenFitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedOpenFitFromEventFlow
          (realityConstrainedOpenFitToEventFlow x) =
        realityConstrainedOpenFitFromEventFlow
          (realityConstrainedOpenFitToEventFlow y) :=
    congrArg realityConstrainedOpenFitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedOpenFit_round_trip x).symm
      (Eq.trans hread (realityConstrainedOpenFit_round_trip y)))

private theorem realityConstrainedOpenFit_fields_faithful :
    ∀ x y : RealityConstrainedOpenFitUp,
      realityConstrainedOpenFitFields x = realityConstrainedOpenFitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ Pi₁ O₁ M₁ F₁ Q₁ L₁ R₁ N₁ =>
      cases y with
      | mk H₂ Pi₂ O₂ M₂ F₂ Q₂ L₂ R₂ N₂ =>
          injection hfields with hH tail0
          injection tail0 with hPi tail1
          injection tail1 with hO tail2
          injection tail2 with hM tail3
          injection tail3 with hF tail4
          injection tail4 with hQ tail5
          injection tail5 with hL tail6
          injection tail6 with hR tail7
          injection tail7 with hN _
          subst hH
          subst hPi
          subst hO
          subst hM
          subst hF
          subst hQ
          subst hL
          subst hR
          subst hN
          rfl

instance realityConstrainedOpenFitBHistCarrier :
    BHistCarrier RealityConstrainedOpenFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedOpenFitToEventFlow
  fromEventFlow := realityConstrainedOpenFitFromEventFlow

instance realityConstrainedOpenFitChapterTasteGate :
    ChapterTasteGate RealityConstrainedOpenFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedOpenFitFromEventFlow
        (realityConstrainedOpenFitToEventFlow x) = some x
    exact realityConstrainedOpenFit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedOpenFitToEventFlow_injective heq)

instance realityConstrainedOpenFitFieldFaithful :
    FieldFaithful RealityConstrainedOpenFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedOpenFitFields
  field_faithful := realityConstrainedOpenFit_fields_faithful

instance realityConstrainedOpenFitNontrivial : Nontrivial RealityConstrainedOpenFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedOpenFitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedOpenFitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedOpenFitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedOpenFitChapterTasteGate

theorem RealityConstrainedOpenFitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedOpenFitDecodeBHist
        (realityConstrainedOpenFitEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedOpenFitUp,
        realityConstrainedOpenFitFromEventFlow
          (realityConstrainedOpenFitToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedOpenFitUp,
          realityConstrainedOpenFitToEventFlow x =
            realityConstrainedOpenFitToEventFlow y → x = y) ∧
          realityConstrainedOpenFitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realityConstrainedOpenFit_decode_encode_bhist
  · constructor
    · exact realityConstrainedOpenFit_round_trip
    · constructor
      · intro x y heq
        exact realityConstrainedOpenFitToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealityConstrainedOpenFitUp
