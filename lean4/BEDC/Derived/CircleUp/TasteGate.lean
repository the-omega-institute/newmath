import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CircleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CircleUp : Type where
  | mk (boundary coordinate metric compactness handoff : BHist) : CircleUp
  deriving DecidableEq

def circleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: circleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: circleEncodeBHist h

def circleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (circleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (circleDecodeBHist tail)

private theorem CircleUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, circleDecodeBHist (circleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def circleFields : CircleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CircleUp.mk boundary coordinate metric compactness handoff =>
      [boundary, coordinate, metric, compactness, handoff]

def circleToEventFlow : CircleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (circleFields x).map circleEncodeBHist

private def circleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => circleEventAt index rest

def circleFromEventFlow (ef : EventFlow) : Option CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CircleUp.mk
      (circleDecodeBHist (circleEventAt 0 ef))
      (circleDecodeBHist (circleEventAt 1 ef))
      (circleDecodeBHist (circleEventAt 2 ef))
      (circleDecodeBHist (circleEventAt 3 ef))
      (circleDecodeBHist (circleEventAt 4 ef)))

private theorem CircleUpTasteGate_single_carrier_alignment_round_trip
    (x : CircleUp) :
    circleFromEventFlow (circleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk boundary coordinate metric compactness handoff =>
      change
        some
          (CircleUp.mk
            (circleDecodeBHist (circleEncodeBHist boundary))
            (circleDecodeBHist (circleEncodeBHist coordinate))
            (circleDecodeBHist (circleEncodeBHist metric))
            (circleDecodeBHist (circleEncodeBHist compactness))
            (circleDecodeBHist (circleEncodeBHist handoff))) =
          some (CircleUp.mk boundary coordinate metric compactness handoff)
      rw [CircleUpTasteGate_single_carrier_alignment_decode_encode boundary,
        CircleUpTasteGate_single_carrier_alignment_decode_encode coordinate,
        CircleUpTasteGate_single_carrier_alignment_decode_encode metric,
        CircleUpTasteGate_single_carrier_alignment_decode_encode compactness,
        CircleUpTasteGate_single_carrier_alignment_decode_encode handoff]

private theorem circleToEventFlow_injective {x y : CircleUp} :
    circleToEventFlow x = circleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      circleFromEventFlow (circleToEventFlow x) =
        circleFromEventFlow (circleToEventFlow y) :=
    congrArg circleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CircleUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CircleUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem CircleUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CircleUp, circleFields x = circleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundary1 coordinate1 metric1 compactness1 handoff1 =>
      cases y with
      | mk boundary2 coordinate2 metric2 compactness2 handoff2 =>
          cases hfields
          rfl

instance circleBHistCarrier : BHistCarrier CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := circleToEventFlow
  fromEventFlow := circleFromEventFlow

instance circleChapterTasteGate : ChapterTasteGate CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change circleFromEventFlow (circleToEventFlow x) = some x
    exact CircleUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (circleToEventFlow_injective heq)

instance circleFieldFaithful : FieldFaithful CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := circleFields
  field_faithful := CircleUpTasteGate_single_carrier_alignment_fields_faithful

instance circleNontrivial : Nontrivial CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CircleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CircleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  circleChapterTasteGate

theorem CircleUpTasteGate_single_carrier_alignment :
    (∀ x : CircleUp, circleFromEventFlow (circleToEventFlow x) = some x) ∧
      (∀ x y : CircleUp, circleToEventFlow x = circleToEventFlow y → x = y) ∧
      circleFields (CircleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨CircleUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => circleToEventFlow_injective heq),
      rfl⟩

theorem CircleSOneBoundaryHandoff
    {B R M K S H P N handoffRead : BHist} :
    UnaryHistory B → UnaryHistory R → UnaryHistory M → UnaryHistory K →
      UnaryHistory S → UnaryHistory H → UnaryHistory P → UnaryHistory N →
        Cont K S handoffRead → hsame H P →
          SemanticNameCert
            (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row B ∨ hsame row R ∨ hsame row M ∨ hsame row K ∨ hsame row S ∨
                hsame row handoffRead)
            (fun row : BHist => UnaryHistory row ∧ Cont K S handoffRead ∧ hsame H P)
            hsame ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CircleUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro _boundaryUnary _realUnary _metricUnary compactUnary soneUnary _transportUnary
    _provenanceUnary _nameUnary handoffRoute sameHP
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed compactUnary soneUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row R ∨ hsame row M ∨ hsame row K ∨ hsame row S ∨
              hsame row handoffRead)
          (fun row : BHist => UnaryHistory row ∧ Cont K S handoffRead ∧ hsame H P)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr sourceData.left))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, handoffRoute, sameHP⟩
  }
  exact ⟨cert, handoffUnary⟩

theorem CircleMetricSubspaceCarrierObligation
    {B R M K S H P N boundaryRead compactMetricRead : BHist} :
    UnaryHistory B → UnaryHistory R → UnaryHistory M → UnaryHistory K →
      UnaryHistory S → UnaryHistory H → UnaryHistory P → UnaryHistory N →
        Cont B M boundaryRead → Cont boundaryRead K compactMetricRead →
          SemanticNameCert
            (fun row : BHist => hsame row compactMetricRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row B ∨ hsame row R ∨ hsame row M ∨ hsame row K ∨ hsame row S ∨
                hsame row H ∨ hsame row P ∨ hsame row N ∨ hsame row compactMetricRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont B M boundaryRead ∧ Cont boundaryRead K compactMetricRead)
            hsame ∧ UnaryHistory compactMetricRead := by
  -- BEDC touchpoint anchor: CircleUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro boundaryUnary _realUnary metricUnary compactUnary _soneUnary _transportUnary
    _provenanceUnary _nameUnary boundaryRoute compactMetricRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary metricUnary boundaryRoute
  have compactMetricUnary : UnaryHistory compactMetricRead :=
    unary_cont_closed boundaryReadUnary compactUnary compactMetricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactMetricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row R ∨ hsame row M ∨ hsame row K ∨ hsame row S ∨
              hsame row H ∨ hsame row P ∨ hsame row N ∨ hsame row compactMetricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B M boundaryRead ∧ Cont boundaryRead K compactMetricRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactMetricRead
        ⟨hsame_refl compactMetricRead, compactMetricUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceData.left)))))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, boundaryRoute, compactMetricRoute⟩
  }
  exact ⟨cert, compactMetricUnary⟩

end BEDC.Derived.CircleUp
