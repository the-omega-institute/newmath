import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SorgenfreyLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SorgenfreyLineUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (R I W A L H C P N : BHist) → SorgenfreyLineUp
  deriving DecidableEq

def sorgenfreyLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sorgenfreyLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sorgenfreyLineEncodeBHist h

def sorgenfreyLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sorgenfreyLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sorgenfreyLineDecodeBHist tail)

private theorem SorgenfreyLineTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sorgenfreyLineFields : SorgenfreyLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SorgenfreyLineUp.mk R I W A L H C P N => [R, I, W, A, L, H, C, P, N]

def sorgenfreyLineToEventFlow : SorgenfreyLineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map sorgenfreyLineEncodeBHist (sorgenfreyLineFields x)

def sorgenfreyLineFromEventFlow : EventFlow → Option SorgenfreyLineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
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
                                            (SorgenfreyLineUp.mk
                                              (sorgenfreyLineDecodeBHist R)
                                              (sorgenfreyLineDecodeBHist I)
                                              (sorgenfreyLineDecodeBHist W)
                                              (sorgenfreyLineDecodeBHist A)
                                              (sorgenfreyLineDecodeBHist L)
                                              (sorgenfreyLineDecodeBHist H)
                                              (sorgenfreyLineDecodeBHist C)
                                              (sorgenfreyLineDecodeBHist P)
                                              (sorgenfreyLineDecodeBHist N))
                                      | _ :: _ => none

private theorem SorgenfreyLineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SorgenfreyLineUp,
      sorgenfreyLineFromEventFlow (sorgenfreyLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R I W A L H C P N =>
      change
        some
          (SorgenfreyLineUp.mk
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist R))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist I))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist W))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist A))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist L))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist H))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist C))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist P))
            (sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist N))) =
          some (SorgenfreyLineUp.mk R I W A L H C P N)
      rw [SorgenfreyLineTasteGate_single_carrier_alignment_decode R,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode I,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode W,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode A,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode L,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode H,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode C,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode P,
        SorgenfreyLineTasteGate_single_carrier_alignment_decode N]

private theorem SorgenfreyLineTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SorgenfreyLineUp} :
    sorgenfreyLineToEventFlow x = sorgenfreyLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sorgenfreyLineFromEventFlow (sorgenfreyLineToEventFlow x) =
        sorgenfreyLineFromEventFlow (sorgenfreyLineToEventFlow y) :=
    congrArg sorgenfreyLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SorgenfreyLineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SorgenfreyLineTasteGate_single_carrier_alignment_round_trip y)))

private theorem SorgenfreyLineTasteGate_single_carrier_alignment_fields_faithful
    (x y : SorgenfreyLineUp) :
    sorgenfreyLineFields x = sorgenfreyLineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk R₁ I₁ W₁ A₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ I₂ W₂ A₂ L₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hI tail1
          injection tail1 with hW tail2
          injection tail2 with hA tail3
          injection tail3 with hL tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hR
          subst hI
          subst hW
          subst hA
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance sorgenfreyLineBHistCarrier : BHistCarrier SorgenfreyLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sorgenfreyLineToEventFlow
  fromEventFlow := sorgenfreyLineFromEventFlow

instance sorgenfreyLineChapterTasteGate : ChapterTasteGate SorgenfreyLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sorgenfreyLineFromEventFlow (sorgenfreyLineToEventFlow x) = some x
    exact SorgenfreyLineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SorgenfreyLineTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sorgenfreyLineFieldFaithful : FieldFaithful SorgenfreyLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sorgenfreyLineFields
  field_faithful := SorgenfreyLineTasteGate_single_carrier_alignment_fields_faithful

instance sorgenfreyLineNontrivial : Nontrivial SorgenfreyLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SorgenfreyLineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SorgenfreyLineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SorgenfreyLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sorgenfreyLineChapterTasteGate

theorem SorgenfreyLineTasteGate_single_carrier_alignment :
    (∀ h : BHist, sorgenfreyLineDecodeBHist (sorgenfreyLineEncodeBHist h) = h) ∧
      (∀ x : SorgenfreyLineUp,
        sorgenfreyLineFromEventFlow (sorgenfreyLineToEventFlow x) = some x) ∧
        (∀ x y : SorgenfreyLineUp,
          sorgenfreyLineToEventFlow x = sorgenfreyLineToEventFlow y → x = y) ∧
          sorgenfreyLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SorgenfreyLineTasteGate_single_carrier_alignment_decode,
      SorgenfreyLineTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => SorgenfreyLineTasteGate_single_carrier_alignment_toEventFlow_injective h),
      rfl⟩

end BEDC.Derived.SorgenfreyLineUp
