import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealNormalizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealNormalizerUp : Type where
  | mk (S M D Q E H C P N : BHist) : BishopRealNormalizerUp
  deriving DecidableEq

def bishopRealNormalizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealNormalizerEncodeBHist h

def bishopRealNormalizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealNormalizerDecodeBHist tail)

private theorem BishopRealNormalizerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopRealNormalizerDecodeBHist (bishopRealNormalizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealNormalizerFields : BishopRealNormalizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealNormalizerUp.mk S M D Q E H C P N => [S, M, D, Q, E, H, C, P, N]

def bishopRealNormalizerToEventFlow : BishopRealNormalizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealNormalizerFields x).map bishopRealNormalizerEncodeBHist

def bishopRealNormalizerFromEventFlow : EventFlow → Option BishopRealNormalizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | M :: restM =>
          match restM with
          | D :: restD =>
              match restD with
              | Q :: restQ =>
                  match restQ with
                  | E :: restE =>
                      match restE with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (BishopRealNormalizerUp.mk
                                              (bishopRealNormalizerDecodeBHist S)
                                              (bishopRealNormalizerDecodeBHist M)
                                              (bishopRealNormalizerDecodeBHist D)
                                              (bishopRealNormalizerDecodeBHist Q)
                                              (bishopRealNormalizerDecodeBHist E)
                                              (bishopRealNormalizerDecodeBHist H)
                                              (bishopRealNormalizerDecodeBHist C)
                                              (bishopRealNormalizerDecodeBHist P)
                                              (bishopRealNormalizerDecodeBHist N))
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

private theorem bishopRealNormalizer_mk_congr
    {S S' M M' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hD : D' = D) (hQ : Q' = Q)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    BishopRealNormalizerUp.mk S' M' D' Q' E' H' C' P' N' =
      BishopRealNormalizerUp.mk S M D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem BishopRealNormalizerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealNormalizerUp,
      bishopRealNormalizerFromEventFlow (bishopRealNormalizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D Q E H C P N =>
      exact
        congrArg some
          (bishopRealNormalizer_mk_congr
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode S)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode M)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode D)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode Q)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode E)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode H)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode C)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode P)
            (BishopRealNormalizerTasteGate_single_carrier_alignment_decode N))

private theorem bishopRealNormalizerToEventFlow_injective
    {x y : BishopRealNormalizerUp} :
    bishopRealNormalizerToEventFlow x = bishopRealNormalizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealNormalizerFromEventFlow (bishopRealNormalizerToEventFlow x) =
        bishopRealNormalizerFromEventFlow (bishopRealNormalizerToEventFlow y) :=
    congrArg bishopRealNormalizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopRealNormalizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopRealNormalizerTasteGate_single_carrier_alignment_round_trip y)))

private theorem bishopRealNormalizer_field_faithful :
    ∀ x y : BishopRealNormalizerUp, bishopRealNormalizerFields x = bishopRealNormalizerFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ D₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ D₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopRealNormalizerBHistCarrier : BHistCarrier BishopRealNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealNormalizerToEventFlow
  fromEventFlow := bishopRealNormalizerFromEventFlow

instance bishopRealNormalizerChapterTasteGate :
    ChapterTasteGate BishopRealNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealNormalizerFromEventFlow (bishopRealNormalizerToEventFlow x) = some x
    exact BishopRealNormalizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRealNormalizerToEventFlow_injective heq)

instance bishopRealNormalizerFieldFaithful : FieldFaithful BishopRealNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealNormalizerFields
  field_faithful := bishopRealNormalizer_field_faithful

instance bishopRealNormalizerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopRealNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRealNormalizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRealNormalizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopRealNormalizerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopRealNormalizerUp) ∧
      Nonempty (FieldFaithful BishopRealNormalizerUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopRealNormalizerUp) ∧
          (∀ h : BHist,
            bishopRealNormalizerDecodeBHist (bishopRealNormalizerEncodeBHist h) = h) ∧
            (∀ x : BishopRealNormalizerUp,
              bishopRealNormalizerFromEventFlow (bishopRealNormalizerToEventFlow x) = some x) ∧
              bishopRealNormalizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨bishopRealNormalizerChapterTasteGate⟩
  · constructor
    · exact ⟨bishopRealNormalizerFieldFaithful⟩
    · constructor
      · exact ⟨bishopRealNormalizerNontrivial⟩
      · constructor
        · exact BishopRealNormalizerTasteGate_single_carrier_alignment_decode
        · constructor
          · exact BishopRealNormalizerTasteGate_single_carrier_alignment_round_trip
          · rfl

end BEDC.Derived.BishopRealNormalizerUp
