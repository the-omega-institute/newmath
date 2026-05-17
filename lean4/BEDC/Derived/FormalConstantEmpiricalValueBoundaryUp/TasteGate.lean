import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalConstantEmpiricalValueBoundaryUp : Type where
  | mk (F E U I R G H C P N : BHist) : FormalConstantEmpiricalValueBoundaryUp
  deriving DecidableEq

def formalConstantEmpiricalValueBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalConstantEmpiricalValueBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalConstantEmpiricalValueBoundaryEncodeBHist h

def formalConstantEmpiricalValueBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalConstantEmpiricalValueBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalConstantEmpiricalValueBoundaryDecodeBHist tail)

private theorem FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      formalConstantEmpiricalValueBoundaryDecodeBHist
        (formalConstantEmpiricalValueBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def formalConstantEmpiricalValueBoundaryFields :
    FormalConstantEmpiricalValueBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FormalConstantEmpiricalValueBoundaryUp.mk F E U I R G H C P N =>
      [F, E, U, I, R, G, H, C, P, N]

def formalConstantEmpiricalValueBoundaryToEventFlow :
    FormalConstantEmpiricalValueBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (formalConstantEmpiricalValueBoundaryFields x).map
        formalConstantEmpiricalValueBoundaryEncodeBHist

def formalConstantEmpiricalValueBoundaryFromEventFlow :
    EventFlow → Option FormalConstantEmpiricalValueBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
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
                                                (FormalConstantEmpiricalValueBoundaryUp.mk
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist F)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist E)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist U)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist I)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist R)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist G)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist H)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist C)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist P)
                                                  (formalConstantEmpiricalValueBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FormalConstantEmpiricalValueBoundaryUp,
      formalConstantEmpiricalValueBoundaryFromEventFlow
        (formalConstantEmpiricalValueBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F E U I R G H C P N =>
      change
        some
          (FormalConstantEmpiricalValueBoundaryUp.mk
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist F))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist E))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist U))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist I))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist R))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist G))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist H))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist C))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist P))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist N))) =
          some (FormalConstantEmpiricalValueBoundaryUp.mk F E U I R G H C P N)
      rw [FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode F,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode E,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode U,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode I,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode R,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode G,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode H,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode C,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode P,
        FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem formalConstantEmpiricalValueBoundaryToEventFlow_injective
    {x y : FormalConstantEmpiricalValueBoundaryUp} :
    formalConstantEmpiricalValueBoundaryToEventFlow x =
        formalConstantEmpiricalValueBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow x) =
        formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow y) :=
    congrArg formalConstantEmpiricalValueBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem formalConstantEmpiricalValueBoundary_fields_faithful :
    ∀ x y : FormalConstantEmpiricalValueBoundaryUp,
      formalConstantEmpiricalValueBoundaryFields x =
          formalConstantEmpiricalValueBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 E1 U1 I1 R1 G1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 E2 U2 I2 R2 G2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance formalConstantEmpiricalValueBoundaryBHistCarrier :
    BHistCarrier FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalConstantEmpiricalValueBoundaryToEventFlow
  fromEventFlow := formalConstantEmpiricalValueBoundaryFromEventFlow

instance formalConstantEmpiricalValueBoundaryChapterTasteGate :
    ChapterTasteGate FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      formalConstantEmpiricalValueBoundaryFromEventFlow
        (formalConstantEmpiricalValueBoundaryToEventFlow x) = some x
    exact FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (formalConstantEmpiricalValueBoundaryToEventFlow_injective heq)

instance formalConstantEmpiricalValueBoundaryFieldFaithful :
    FieldFaithful FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := formalConstantEmpiricalValueBoundaryFields
  field_faithful := formalConstantEmpiricalValueBoundary_fields_faithful

instance formalConstantEmpiricalValueBoundaryNontrivial :
    Nontrivial FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FormalConstantEmpiricalValueBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FormalConstantEmpiricalValueBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FormalConstantEmpiricalValueBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  formalConstantEmpiricalValueBoundaryChapterTasteGate

theorem FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        formalConstantEmpiricalValueBoundaryDecodeBHist
          (formalConstantEmpiricalValueBoundaryEncodeBHist h) = h) ∧
      (∀ x : FormalConstantEmpiricalValueBoundaryUp,
        formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow x) = some x) ∧
        (∀ x y : FormalConstantEmpiricalValueBoundaryUp,
          formalConstantEmpiricalValueBoundaryToEventFlow x =
              formalConstantEmpiricalValueBoundaryToEventFlow y →
            x = y) ∧
          formalConstantEmpiricalValueBoundaryEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_decode,
      FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => formalConstantEmpiricalValueBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp
