import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTranslationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTranslationUp : Type where
  | mk (X Q WX WQ DX DQ A E R Z H C P N : BHist) : RegularCauchyTranslationUp
  deriving DecidableEq

def regularCauchyTranslationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTranslationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTranslationEncodeBHist h

def regularCauchyTranslationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTranslationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTranslationDecodeBHist tail)

private theorem RegularCauchyTranslationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchyTranslationDecodeBHist
      (regularCauchyTranslationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyTranslationTasteGate_single_carrier_alignment_fields :
    RegularCauchyTranslationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTranslationUp.mk X Q WX WQ DX DQ A E R Z H C P N =>
      [X, Q, WX, WQ, DX, DQ, A, E, R, Z, H, C, P, N]

def regularCauchyTranslationToEventFlow : RegularCauchyTranslationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTranslationUp.mk X Q WX WQ DX DQ A E R Z H C P N =>
      [regularCauchyTranslationEncodeBHist X, regularCauchyTranslationEncodeBHist Q,
        regularCauchyTranslationEncodeBHist WX, regularCauchyTranslationEncodeBHist WQ,
        regularCauchyTranslationEncodeBHist DX, regularCauchyTranslationEncodeBHist DQ,
        regularCauchyTranslationEncodeBHist A, regularCauchyTranslationEncodeBHist E,
        regularCauchyTranslationEncodeBHist R, regularCauchyTranslationEncodeBHist Z,
        regularCauchyTranslationEncodeBHist H, regularCauchyTranslationEncodeBHist C,
        regularCauchyTranslationEncodeBHist P, regularCauchyTranslationEncodeBHist N]

def regularCauchyTranslationFromEventFlow : EventFlow → Option RegularCauchyTranslationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest =>
      match rest with
      | [] => none
      | Q :: rest =>
          match rest with
          | [] => none
          | WX :: rest =>
              match rest with
              | [] => none
              | WQ :: rest =>
                  match rest with
                  | [] => none
                  | DX :: rest =>
                      match rest with
                      | [] => none
                      | DQ :: rest =>
                          match rest with
                          | [] => none
                          | A :: rest =>
                              match rest with
                              | [] => none
                              | E :: rest =>
                                  match rest with
                                  | [] => none
                                  | R :: rest =>
                                      match rest with
                                      | [] => none
                                      | Z :: rest =>
                                          match rest with
                                          | [] => none
                                          | H :: rest =>
                                              match rest with
                                              | [] => none
                                              | C :: rest =>
                                                  match rest with
                                                  | [] => none
                                                  | P :: rest =>
                                                      match rest with
                                                      | [] => none
                                                      | N :: rest =>
                                                          match rest with
                                                          | [] =>
                                                              some
                                                                (RegularCauchyTranslationUp.mk
                                                                  (regularCauchyTranslationDecodeBHist X)
                                                                  (regularCauchyTranslationDecodeBHist Q)
                                                                  (regularCauchyTranslationDecodeBHist WX)
                                                                  (regularCauchyTranslationDecodeBHist WQ)
                                                                  (regularCauchyTranslationDecodeBHist DX)
                                                                  (regularCauchyTranslationDecodeBHist DQ)
                                                                  (regularCauchyTranslationDecodeBHist A)
                                                                  (regularCauchyTranslationDecodeBHist E)
                                                                  (regularCauchyTranslationDecodeBHist R)
                                                                  (regularCauchyTranslationDecodeBHist Z)
                                                                  (regularCauchyTranslationDecodeBHist H)
                                                                  (regularCauchyTranslationDecodeBHist C)
                                                                  (regularCauchyTranslationDecodeBHist P)
                                                                  (regularCauchyTranslationDecodeBHist N))
                                                          | _ :: _ => none

private theorem RegularCauchyTranslationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyTranslationUp,
      regularCauchyTranslationFromEventFlow (regularCauchyTranslationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Q WX WQ DX DQ A E R Z H C P N =>
      rw [regularCauchyTranslationToEventFlow, regularCauchyTranslationFromEventFlow,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode X,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode WX,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode WQ,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode DX,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode DQ,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode A,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode E,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode R,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode Z,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode H,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode C,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode P,
        RegularCauchyTranslationTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyTranslationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTranslationUp} :
    regularCauchyTranslationToEventFlow x = regularCauchyTranslationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTranslationFromEventFlow (regularCauchyTranslationToEventFlow x) =
        regularCauchyTranslationFromEventFlow (regularCauchyTranslationToEventFlow y) :=
    congrArg regularCauchyTranslationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyTranslationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTranslationTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyTranslationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyTranslationUp,
      RegularCauchyTranslationTasteGate_single_carrier_alignment_fields x =
          RegularCauchyTranslationTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Q₁ WX₁ WQ₁ DX₁ DQ₁ A₁ E₁ R₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Q₂ WX₂ WQ₂ DX₂ DQ₂ A₂ E₂ R₂ Z₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hQ tail1
          injection tail1 with hWX tail2
          injection tail2 with hWQ tail3
          injection tail3 with hDX tail4
          injection tail4 with hDQ tail5
          injection tail5 with hA tail6
          injection tail6 with hE tail7
          injection tail7 with hR tail8
          injection tail8 with hZ tail9
          injection tail9 with hH tail10
          injection tail10 with hC tail11
          injection tail11 with hP tail12
          injection tail12 with hN _
          subst hX
          subst hQ
          subst hWX
          subst hWQ
          subst hDX
          subst hDQ
          subst hA
          subst hE
          subst hR
          subst hZ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyTranslationBHistCarrier : BHistCarrier RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTranslationToEventFlow
  fromEventFlow := regularCauchyTranslationFromEventFlow

instance regularCauchyTranslationChapterTasteGate :
    ChapterTasteGate RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTranslationFromEventFlow
      (regularCauchyTranslationToEventFlow x) = some x
    exact RegularCauchyTranslationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTranslationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyTranslationFieldFaithful :
    FieldFaithful RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegularCauchyTranslationTasteGate_single_carrier_alignment_fields
  field_faithful := RegularCauchyTranslationTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyTranslationNontrivial : Nontrivial RegularCauchyTranslationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTranslationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTranslationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchyTranslationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyTranslationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTranslationChapterTasteGate

theorem RegularCauchyTranslationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTranslationDecodeBHist (regularCauchyTranslationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTranslationUp,
        regularCauchyTranslationFromEventFlow (regularCauchyTranslationToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyTranslationUp,
        regularCauchyTranslationToEventFlow x = regularCauchyTranslationToEventFlow y →
          x = y) ∧
      regularCauchyTranslationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyTranslationTasteGate_single_carrier_alignment_decode,
      RegularCauchyTranslationTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RegularCauchyTranslationTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyTranslationUp
