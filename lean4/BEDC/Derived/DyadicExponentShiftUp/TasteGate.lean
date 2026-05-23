import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicExponentShiftUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicExponentShiftUp : Type where
  | mk (M U K S D T F H C P N : BHist) : DyadicExponentShiftUp
  deriving DecidableEq

def dyadicExponentShiftEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicExponentShiftEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicExponentShiftEncodeBHist h

def dyadicExponentShiftDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicExponentShiftDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicExponentShiftDecodeBHist tail)

private theorem DyadicExponentShiftTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicExponentShiftDecodeBHist (dyadicExponentShiftEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicExponentShiftFields : DyadicExponentShiftUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicExponentShiftUp.mk M U K S D T F H C P N => [M, U, K, S, D, T, F, H, C, P, N]

def dyadicExponentShiftToEventFlow : DyadicExponentShiftUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicExponentShiftFields x).map dyadicExponentShiftEncodeBHist

def dyadicExponentShiftFromEventFlow : EventFlow → Option DyadicExponentShiftUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | U :: restU =>
          match restU with
          | K :: restK =>
              match restK with
              | S :: restS =>
                  match restS with
                  | D :: restD =>
                      match restD with
                      | T :: restT =>
                          match restT with
                          | F :: restF =>
                              match restF with
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
                                                    (DyadicExponentShiftUp.mk
                                                      (dyadicExponentShiftDecodeBHist M)
                                                      (dyadicExponentShiftDecodeBHist U)
                                                      (dyadicExponentShiftDecodeBHist K)
                                                      (dyadicExponentShiftDecodeBHist S)
                                                      (dyadicExponentShiftDecodeBHist D)
                                                      (dyadicExponentShiftDecodeBHist T)
                                                      (dyadicExponentShiftDecodeBHist F)
                                                      (dyadicExponentShiftDecodeBHist H)
                                                      (dyadicExponentShiftDecodeBHist C)
                                                      (dyadicExponentShiftDecodeBHist P)
                                                      (dyadicExponentShiftDecodeBHist N))
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

private theorem dyadicExponentShift_mk_congr
    {M M' U U' K K' S S' D D' T T' F F' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hU : U' = U) (hK : K' = K) (hS : S' = S)
    (hD : D' = D) (hT : T' = T) (hF : F' = F) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    DyadicExponentShiftUp.mk M' U' K' S' D' T' F' H' C' P' N' =
      DyadicExponentShiftUp.mk M U K S D T F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hU
  cases hK
  cases hS
  cases hD
  cases hT
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem DyadicExponentShiftTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicExponentShiftUp,
      dyadicExponentShiftFromEventFlow (dyadicExponentShiftToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U K S D T F H C P N =>
      exact
        congrArg some
          (dyadicExponentShift_mk_congr
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode M)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode U)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode K)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode S)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode D)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode T)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode F)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode H)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode C)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode P)
            (DyadicExponentShiftTasteGate_single_carrier_alignment_decode N))

private theorem dyadicExponentShiftToEventFlow_injective
    {x y : DyadicExponentShiftUp} :
    dyadicExponentShiftToEventFlow x = dyadicExponentShiftToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicExponentShiftFromEventFlow (dyadicExponentShiftToEventFlow x) =
        dyadicExponentShiftFromEventFlow (dyadicExponentShiftToEventFlow y) :=
    congrArg dyadicExponentShiftFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicExponentShiftTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicExponentShiftTasteGate_single_carrier_alignment_round_trip y)))

private theorem dyadicExponentShift_field_faithful :
    ∀ x y : DyadicExponentShiftUp, dyadicExponentShiftFields x = dyadicExponentShiftFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ U₁ K₁ S₁ D₁ T₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ U₂ K₂ S₂ D₂ T₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicExponentShiftBHistCarrier : BHistCarrier DyadicExponentShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicExponentShiftToEventFlow
  fromEventFlow := dyadicExponentShiftFromEventFlow

instance dyadicExponentShiftChapterTasteGate : ChapterTasteGate DyadicExponentShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicExponentShiftFromEventFlow (dyadicExponentShiftToEventFlow x) = some x
    exact DyadicExponentShiftTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicExponentShiftToEventFlow_injective heq)

instance dyadicExponentShiftFieldFaithful : FieldFaithful DyadicExponentShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicExponentShiftFields
  field_faithful := dyadicExponentShift_field_faithful

instance dyadicExponentShiftNontrivial : Nontrivial DyadicExponentShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicExponentShiftUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicExponentShiftUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicExponentShiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicExponentShiftChapterTasteGate

theorem DyadicExponentShiftTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicExponentShiftDecodeBHist (dyadicExponentShiftEncodeBHist h) = h) ∧
      (∀ x : DyadicExponentShiftUp,
        dyadicExponentShiftFromEventFlow (dyadicExponentShiftToEventFlow x) = some x) ∧
        (∀ x y : DyadicExponentShiftUp,
          dyadicExponentShiftToEventFlow x = dyadicExponentShiftToEventFlow y → x = y) ∧
          dyadicExponentShiftEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨DyadicExponentShiftTasteGate_single_carrier_alignment_decode,
      DyadicExponentShiftTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => dyadicExponentShiftToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicExponentShiftUp
