import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEquivalenceUp : Type where
  | mk (X Y W M D T H C P N : BHist) : CauchyTailEquivalenceUp
  deriving DecidableEq

def cauchyTailEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailEquivalenceEncodeBHist h

def cauchyTailEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailEquivalenceDecodeBHist tail)

private theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailEquivalenceFields : CauchyTailEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEquivalenceUp.mk X Y W M D T H C P N => [X, Y, W, M, D, T, H, C, P, N]

def cauchyTailEquivalenceToEventFlow : CauchyTailEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailEquivalenceFields x).map cauchyTailEquivalenceEncodeBHist

def cauchyTailEquivalenceFromEventFlow : EventFlow → Option CauchyTailEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | Y :: restY =>
          match restY with
          | W :: restW =>
              match restW with
              | M :: restM =>
                  match restM with
                  | D :: restD =>
                      match restD with
                      | T :: restT =>
                          match restT with
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
                                                (CauchyTailEquivalenceUp.mk
                                                  (cauchyTailEquivalenceDecodeBHist X)
                                                  (cauchyTailEquivalenceDecodeBHist Y)
                                                  (cauchyTailEquivalenceDecodeBHist W)
                                                  (cauchyTailEquivalenceDecodeBHist M)
                                                  (cauchyTailEquivalenceDecodeBHist D)
                                                  (cauchyTailEquivalenceDecodeBHist T)
                                                  (cauchyTailEquivalenceDecodeBHist H)
                                                  (cauchyTailEquivalenceDecodeBHist C)
                                                  (cauchyTailEquivalenceDecodeBHist P)
                                                  (cauchyTailEquivalenceDecodeBHist N))
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

private theorem cauchyTailEquivalence_mk_congr
    {X X' Y Y' W W' M M' D D' T T' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hW : W' = W) (hM : M' = M)
    (hD : D' = D) (hT : T' = T) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyTailEquivalenceUp.mk X' Y' W' M' D' T' H' C' P' N' =
      CauchyTailEquivalenceUp.mk X Y W M D T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hW
  cases hM
  cases hD
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyTailEquivalenceUp,
      cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W M D T H C P N =>
      exact
        congrArg some
          (cauchyTailEquivalence_mk_congr
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode X)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode Y)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode W)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode M)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode D)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode T)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode H)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode C)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode P)
            (CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode N))

private theorem cauchyTailEquivalenceToEventFlow_injective {x y : CauchyTailEquivalenceUp} :
    cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) =
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow y) :=
    congrArg cauchyTailEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyTailEquivalence_fields_faithful :
    ∀ x y : CauchyTailEquivalenceUp,
      cauchyTailEquivalenceFields x = cauchyTailEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X₁ Y₁ W₁ M₁ D₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ W₂ M₂ D₂ T₂ H₂ C₂ P₂ N₂ =>
          injection h with hX restX
          injection restX with hY restY
          injection restY with hW restW
          injection restW with hM restM
          injection restM with hD restD
          injection restD with hT restT
          injection restT with hH restH
          injection restH with hC restC
          injection restC with hP restP
          injection restP with hN _
          exact
            cauchyTailEquivalence_mk_congr hX hY hW hM hD hT hH hC hP hN

instance cauchyTailEquivalenceBHistCarrier : BHistCarrier CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailEquivalenceToEventFlow
  fromEventFlow := cauchyTailEquivalenceFromEventFlow

instance cauchyTailEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x
    exact CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailEquivalenceToEventFlow_injective heq)

instance cauchyTailEquivalenceFieldFaithful : FieldFaithful CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailEquivalenceFields
  field_faithful := cauchyTailEquivalence_fields_faithful

instance cauchyTailEquivalenceNontrivial : Nontrivial CauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyTailEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailEquivalenceChapterTasteGate

theorem CauchyTailEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyTailEquivalenceDecodeBHist (cauchyTailEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchyTailEquivalenceUp,
        cauchyTailEquivalenceFromEventFlow (cauchyTailEquivalenceToEventFlow x) = some x) ∧
      (∀ x y : CauchyTailEquivalenceUp,
        cauchyTailEquivalenceToEventFlow x = cauchyTailEquivalenceToEventFlow y → x = y) ∧
      cauchyTailEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyTailEquivalenceTasteGate_single_carrier_alignment_decode,
      CauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyTailEquivalenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyTailEquivalenceUp
