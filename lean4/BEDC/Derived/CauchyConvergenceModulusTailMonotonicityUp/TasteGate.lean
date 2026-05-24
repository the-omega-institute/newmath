import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyConvergenceModulusTailMonotonicityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyConvergenceModulusTailMonotonicityUp : Type where
  | mk (K0 T W R D L H C P N : BHist) : CauchyConvergenceModulusTailMonotonicityUp
  deriving DecidableEq

def cauchyConvergenceModulusTailMonotonicityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyConvergenceModulusTailMonotonicityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyConvergenceModulusTailMonotonicityEncodeBHist h

def cauchyConvergenceModulusTailMonotonicityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyConvergenceModulusTailMonotonicityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyConvergenceModulusTailMonotonicityDecodeBHist tail)

private theorem CauchyConvergenceModulusTailMonotonicityTasteGate_decode :
    forall h : BHist,
      cauchyConvergenceModulusTailMonotonicityDecodeBHist
          (cauchyConvergenceModulusTailMonotonicityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyConvergenceModulusTailMonotonicityFields :
    CauchyConvergenceModulusTailMonotonicityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyConvergenceModulusTailMonotonicityUp.mk K0 T W R D L H C P N =>
      [K0, T, W, R, D, L, H, C, P, N]

def cauchyConvergenceModulusTailMonotonicityToEventFlow :
    CauchyConvergenceModulusTailMonotonicityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyConvergenceModulusTailMonotonicityFields x).map
        cauchyConvergenceModulusTailMonotonicityEncodeBHist

def cauchyConvergenceModulusTailMonotonicityFromEventFlow :
    EventFlow -> Option CauchyConvergenceModulusTailMonotonicityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
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
                                                (CauchyConvergenceModulusTailMonotonicityUp.mk
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist K0)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist T)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist W)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist R)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist D)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist L)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist H)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist C)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist P)
                                                  (cauchyConvergenceModulusTailMonotonicityDecodeBHist N))
                                          | _ :: _ => none

private theorem CauchyConvergenceModulusTailMonotonicityTasteGate_round_trip :
    forall x : CauchyConvergenceModulusTailMonotonicityUp,
      cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K0 T W R D L H C P N =>
      change
        some
          (CauchyConvergenceModulusTailMonotonicityUp.mk
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist K0))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist T))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist W))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist R))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist D))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist L))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist H))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist C))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist P))
            (cauchyConvergenceModulusTailMonotonicityDecodeBHist
              (cauchyConvergenceModulusTailMonotonicityEncodeBHist N))) =
          some (CauchyConvergenceModulusTailMonotonicityUp.mk K0 T W R D L H C P N)
      rw [CauchyConvergenceModulusTailMonotonicityTasteGate_decode K0,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode T,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode W,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode R,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode D,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode L,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode H,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode C,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode P,
        CauchyConvergenceModulusTailMonotonicityTasteGate_decode N]

private theorem CauchyConvergenceModulusTailMonotonicityTasteGate_toEventFlow_injective
    {x y : CauchyConvergenceModulusTailMonotonicityUp} :
    cauchyConvergenceModulusTailMonotonicityToEventFlow x =
        cauchyConvergenceModulusTailMonotonicityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow x) =
        cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow y) :=
    congrArg cauchyConvergenceModulusTailMonotonicityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyConvergenceModulusTailMonotonicityTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyConvergenceModulusTailMonotonicityTasteGate_round_trip y)))

private theorem CauchyConvergenceModulusTailMonotonicityTasteGate_fields :
    forall x y : CauchyConvergenceModulusTailMonotonicityUp,
      cauchyConvergenceModulusTailMonotonicityFields x =
          cauchyConvergenceModulusTailMonotonicityFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K01 T1 W1 R1 D1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk K02 T2 W2 R2 D2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyConvergenceModulusTailMonotonicityBHistCarrier :
    BHistCarrier CauchyConvergenceModulusTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyConvergenceModulusTailMonotonicityToEventFlow
  fromEventFlow := cauchyConvergenceModulusTailMonotonicityFromEventFlow

instance cauchyConvergenceModulusTailMonotonicityChapterTasteGate :
    ChapterTasteGate CauchyConvergenceModulusTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyConvergenceModulusTailMonotonicityFromEventFlow
          (cauchyConvergenceModulusTailMonotonicityToEventFlow x) =
        some x
    exact CauchyConvergenceModulusTailMonotonicityTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyConvergenceModulusTailMonotonicityTasteGate_toEventFlow_injective heq)

instance cauchyConvergenceModulusTailMonotonicityFieldFaithful :
    FieldFaithful CauchyConvergenceModulusTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyConvergenceModulusTailMonotonicityFields
  field_faithful := CauchyConvergenceModulusTailMonotonicityTasteGate_fields

instance cauchyConvergenceModulusTailMonotonicityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyConvergenceModulusTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyConvergenceModulusTailMonotonicityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyConvergenceModulusTailMonotonicityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyConvergenceModulusTailMonotonicityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyConvergenceModulusTailMonotonicityChapterTasteGate

namespace TasteGate

theorem CauchyConvergenceModulusTailMonotonicityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyConvergenceModulusTailMonotonicityUp) ∧
      Nonempty (FieldFaithful CauchyConvergenceModulusTailMonotonicityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial
          CauchyConvergenceModulusTailMonotonicityUp) ∧
          (forall h : BHist,
            cauchyConvergenceModulusTailMonotonicityDecodeBHist
                (cauchyConvergenceModulusTailMonotonicityEncodeBHist h) =
              h) ∧
            (forall x : CauchyConvergenceModulusTailMonotonicityUp,
              cauchyConvergenceModulusTailMonotonicityFromEventFlow
                  (cauchyConvergenceModulusTailMonotonicityToEventFlow x) =
                some x) ∧
              (forall x y : CauchyConvergenceModulusTailMonotonicityUp,
                cauchyConvergenceModulusTailMonotonicityToEventFlow x =
                    cauchyConvergenceModulusTailMonotonicityToEventFlow y ->
                  x = y) ∧
                cauchyConvergenceModulusTailMonotonicityEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨cauchyConvergenceModulusTailMonotonicityChapterTasteGate⟩
  · constructor
    · exact ⟨cauchyConvergenceModulusTailMonotonicityFieldFaithful⟩
    · constructor
      · exact ⟨cauchyConvergenceModulusTailMonotonicityNontrivial⟩
      · constructor
        · exact CauchyConvergenceModulusTailMonotonicityTasteGate_decode
        · constructor
          · exact CauchyConvergenceModulusTailMonotonicityTasteGate_round_trip
          · constructor
            · intro x y heq
              exact CauchyConvergenceModulusTailMonotonicityTasteGate_toEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate CauchyConvergenceModulusTailMonotonicityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.CauchyConvergenceModulusTailMonotonicityUp.taste_gate

end TasteGate

end BEDC.Derived.CauchyConvergenceModulusTailMonotonicityUp
