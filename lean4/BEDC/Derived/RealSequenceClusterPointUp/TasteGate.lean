import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequenceClusterPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequenceClusterPointUp : Type where
  | mk (S J W Q D R H C P N : BHist) : RealSequenceClusterPointUp
  deriving DecidableEq

def realSequenceClusterPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSequenceClusterPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSequenceClusterPointEncodeBHist h

def realSequenceClusterPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSequenceClusterPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSequenceClusterPointDecodeBHist tail)

private theorem RealSequenceClusterPointTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realSequenceClusterPointDecodeBHist (realSequenceClusterPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RealSequenceClusterPointTasteGate_single_carrier_alignment_fields :
    RealSequenceClusterPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceClusterPointUp.mk S J W Q D R H C P N => [S, J, W, Q, D, R, H, C, P, N]

def realSequenceClusterPointToEventFlow : RealSequenceClusterPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceClusterPointUp.mk S J W Q D R H C P N =>
      [realSequenceClusterPointEncodeBHist S, realSequenceClusterPointEncodeBHist J,
        realSequenceClusterPointEncodeBHist W, realSequenceClusterPointEncodeBHist Q,
        realSequenceClusterPointEncodeBHist D, realSequenceClusterPointEncodeBHist R,
        realSequenceClusterPointEncodeBHist H, realSequenceClusterPointEncodeBHist C,
        realSequenceClusterPointEncodeBHist P, realSequenceClusterPointEncodeBHist N]

def realSequenceClusterPointFromEventFlow : EventFlow → Option RealSequenceClusterPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: J :: W :: Q :: D :: R :: H :: C :: P :: N :: [] =>
      some
        (RealSequenceClusterPointUp.mk
          (realSequenceClusterPointDecodeBHist S)
          (realSequenceClusterPointDecodeBHist J)
          (realSequenceClusterPointDecodeBHist W)
          (realSequenceClusterPointDecodeBHist Q)
          (realSequenceClusterPointDecodeBHist D)
          (realSequenceClusterPointDecodeBHist R)
          (realSequenceClusterPointDecodeBHist H)
          (realSequenceClusterPointDecodeBHist C)
          (realSequenceClusterPointDecodeBHist P)
          (realSequenceClusterPointDecodeBHist N))
  | _ => none

private theorem RealSequenceClusterPointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealSequenceClusterPointUp,
      realSequenceClusterPointFromEventFlow (realSequenceClusterPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S J W Q D R H C P N =>
      rw [realSequenceClusterPointToEventFlow, realSequenceClusterPointFromEventFlow,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode S,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode J,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode W,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode Q,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode D,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode R,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode H,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode C,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode P,
        RealSequenceClusterPointTasteGate_single_carrier_alignment_decode N]

private theorem RealSequenceClusterPointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSequenceClusterPointUp} :
    realSequenceClusterPointToEventFlow x = realSequenceClusterPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSequenceClusterPointFromEventFlow (realSequenceClusterPointToEventFlow x) =
        realSequenceClusterPointFromEventFlow (realSequenceClusterPointToEventFlow y) :=
    congrArg realSequenceClusterPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealSequenceClusterPointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSequenceClusterPointTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealSequenceClusterPointTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealSequenceClusterPointUp,
      RealSequenceClusterPointTasteGate_single_carrier_alignment_fields x =
          RealSequenceClusterPointTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ J₁ W₁ Q₁ D₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ J₂ W₂ Q₂ D₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hJ tail1
          injection tail1 with hW tail2
          injection tail2 with hQ tail3
          injection tail3 with hD tail4
          injection tail4 with hR tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hJ
          subst hW
          subst hQ
          subst hD
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realSequenceClusterPointBHistCarrier : BHistCarrier RealSequenceClusterPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSequenceClusterPointToEventFlow
  fromEventFlow := realSequenceClusterPointFromEventFlow

instance realSequenceClusterPointChapterTasteGate :
    ChapterTasteGate RealSequenceClusterPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSequenceClusterPointFromEventFlow (realSequenceClusterPointToEventFlow x) = some x
    exact RealSequenceClusterPointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealSequenceClusterPointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realSequenceClusterPointFieldFaithful :
    FieldFaithful RealSequenceClusterPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RealSequenceClusterPointTasteGate_single_carrier_alignment_fields
  field_faithful := RealSequenceClusterPointTasteGate_single_carrier_alignment_fields_faithful

instance realSequenceClusterPointNontrivial :
    Nontrivial RealSequenceClusterPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSequenceClusterPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealSequenceClusterPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealSequenceClusterPointTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealSequenceClusterPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSequenceClusterPointChapterTasteGate

theorem RealSequenceClusterPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSequenceClusterPointDecodeBHist (realSequenceClusterPointEncodeBHist h) = h) ∧
      RealSequenceClusterPointTasteGate_single_carrier_alignment_fields
          (RealSequenceClusterPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealSequenceClusterPointTasteGate_single_carrier_alignment_decode
  · rfl

theorem RealSequenceClusterPointSubsequence_handoff
    {S J W Q D R H C P N selected clusterRoute : BHist} :
    UnaryHistory S ->
      UnaryHistory J ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory H ->
              Cont S J W ->
                Cont W Q D ->
                  Cont D R selected ->
                    Cont selected H clusterRoute ->
                      UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory selected ∧
                        UnaryHistory clusterRoute ∧
                          realSequenceClusterPointToEventFlow
                              (RealSequenceClusterPointUp.mk S J W Q D R H C P N) =
                            realSequenceClusterPointToEventFlow
                              (RealSequenceClusterPointUp.mk S J W Q D R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro sourceUnary indexUnary readbackUnary clusterUnary transportUnary indexRoute windowRoute
    selectedRoute clusterRouteRead
  have windowUnary : UnaryHistory W :=
    unary_cont_closed sourceUnary indexUnary indexRoute
  have dyadicUnary : UnaryHistory D :=
    unary_cont_closed windowUnary readbackUnary windowRoute
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed dyadicUnary clusterUnary selectedRoute
  have clusterRouteUnary : UnaryHistory clusterRoute :=
    unary_cont_closed selectedUnary transportUnary clusterRouteRead
  exact ⟨windowUnary, dyadicUnary, selectedUnary, clusterRouteUnary, rfl⟩

end BEDC.Derived.RealSequenceClusterPointUp
