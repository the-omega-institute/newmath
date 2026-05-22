import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRegularCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRegularCauchySubsequenceUp : Type where
  | mk (B T W D Q R F E H C P N : BHist) : BoundedRegularCauchySubsequenceUp
  deriving DecidableEq

def boundedRegularCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRegularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRegularCauchySubsequenceEncodeBHist h

def boundedRegularCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRegularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRegularCauchySubsequenceDecodeBHist tail)

private theorem BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedRegularCauchySubsequenceDecodeBHist
        (boundedRegularCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRegularCauchySubsequenceFields :
    BoundedRegularCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRegularCauchySubsequenceUp.mk B T W D Q R F E H C P N =>
      [B, T, W, D, Q, R, F, E, H, C, P, N]

def boundedRegularCauchySubsequenceToEventFlow :
    BoundedRegularCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (boundedRegularCauchySubsequenceFields x).map
        boundedRegularCauchySubsequenceEncodeBHist

def boundedRegularCauchySubsequenceFromEventFlow :
    EventFlow → Option BoundedRegularCauchySubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | B :: restB =>
      match restB with
      | T :: restT =>
          match restT with
          | W :: restW =>
              match restW with
              | D :: restD =>
                  match restD with
                  | Q :: restQ =>
                      match restQ with
                      | R :: restR =>
                          match restR with
                          | F :: restF =>
                              match restF with
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
                                                        (BoundedRegularCauchySubsequenceUp.mk
                                                          (boundedRegularCauchySubsequenceDecodeBHist B)
                                                          (boundedRegularCauchySubsequenceDecodeBHist T)
                                                          (boundedRegularCauchySubsequenceDecodeBHist W)
                                                          (boundedRegularCauchySubsequenceDecodeBHist D)
                                                          (boundedRegularCauchySubsequenceDecodeBHist Q)
                                                          (boundedRegularCauchySubsequenceDecodeBHist R)
                                                          (boundedRegularCauchySubsequenceDecodeBHist F)
                                                          (boundedRegularCauchySubsequenceDecodeBHist E)
                                                          (boundedRegularCauchySubsequenceDecodeBHist H)
                                                          (boundedRegularCauchySubsequenceDecodeBHist C)
                                                          (boundedRegularCauchySubsequenceDecodeBHist P)
                                                          (boundedRegularCauchySubsequenceDecodeBHist N))
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
      | [] => none
  | [] => none

private theorem boundedRegularCauchySubsequence_mk_congr
    {B B' T T' W W' D D' Q Q' R R' F F' E E' H H' C C' P P' N N' : BHist}
    (hB : B' = B) (hT : T' = T) (hW : W' = W) (hD : D' = D)
    (hQ : Q' = Q) (hR : R' = R) (hF : F' = F) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    BoundedRegularCauchySubsequenceUp.mk B' T' W' D' Q' R' F' E' H' C' P' N' =
      BoundedRegularCauchySubsequenceUp.mk B T W D Q R F E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hT
  cases hW
  cases hD
  cases hQ
  cases hR
  cases hF
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedRegularCauchySubsequenceUp,
      boundedRegularCauchySubsequenceFromEventFlow
        (boundedRegularCauchySubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B T W D Q R F E H C P N =>
      exact
        congrArg some
          (boundedRegularCauchySubsequence_mk_congr
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode B)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode T)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode W)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode D)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode Q)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode R)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode F)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode E)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode H)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode C)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode P)
            (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode N))

private theorem boundedRegularCauchySubsequenceToEventFlow_injective
    {x y : BoundedRegularCauchySubsequenceUp} :
    boundedRegularCauchySubsequenceToEventFlow x =
      boundedRegularCauchySubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRegularCauchySubsequenceFromEventFlow
          (boundedRegularCauchySubsequenceToEventFlow x) =
        boundedRegularCauchySubsequenceFromEventFlow
          (boundedRegularCauchySubsequenceToEventFlow y) :=
    congrArg boundedRegularCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem boundedRegularCauchySubsequence_field_faithful :
    ∀ x y : BoundedRegularCauchySubsequenceUp,
      boundedRegularCauchySubsequenceFields x =
        boundedRegularCauchySubsequenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ T₁ W₁ D₁ Q₁ R₁ F₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ T₂ W₂ D₂ Q₂ R₂ F₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance boundedRegularCauchySubsequenceBHistCarrier :
    BHistCarrier BoundedRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRegularCauchySubsequenceToEventFlow
  fromEventFlow := boundedRegularCauchySubsequenceFromEventFlow

instance boundedRegularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate BoundedRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedRegularCauchySubsequenceFromEventFlow
        (boundedRegularCauchySubsequenceToEventFlow x) = some x
    exact BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedRegularCauchySubsequenceToEventFlow_injective heq)

instance boundedRegularCauchySubsequenceFieldFaithful :
    FieldFaithful BoundedRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedRegularCauchySubsequenceFields
  field_faithful := boundedRegularCauchySubsequence_field_faithful

instance boundedRegularCauchySubsequenceNontrivial :
    Nontrivial BoundedRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRegularCauchySubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BoundedRegularCauchySubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedRegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRegularCauchySubsequenceChapterTasteGate

theorem BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedRegularCauchySubsequenceDecodeBHist
        (boundedRegularCauchySubsequenceEncodeBHist h) = h) ∧
      (∀ x : BoundedRegularCauchySubsequenceUp,
        boundedRegularCauchySubsequenceFromEventFlow
          (boundedRegularCauchySubsequenceToEventFlow x) = some x) ∧
        (∀ x y : BoundedRegularCauchySubsequenceUp,
          boundedRegularCauchySubsequenceToEventFlow x =
            boundedRegularCauchySubsequenceToEventFlow y → x = y) ∧
          boundedRegularCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode,
      BoundedRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => boundedRegularCauchySubsequenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedRegularCauchySubsequenceUp
