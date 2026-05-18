import BEDC.FKernel.Cont
import BEDC.FKernel.Sig
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeCheckingMembershipTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Sig
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeCheckingMembershipTraceUp : Type where
  | mk : (M D R S H C P N : BHist) → TypeCheckingMembershipTraceUp
  deriving DecidableEq

def typeCheckingMembershipTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeCheckingMembershipTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeCheckingMembershipTraceEncodeBHist h

def typeCheckingMembershipTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeCheckingMembershipTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeCheckingMembershipTraceDecodeBHist tail)

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      typeCheckingMembershipTraceDecodeBHist
        (typeCheckingMembershipTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typeCheckingMembershipTraceFields :
    TypeCheckingMembershipTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingMembershipTraceUp.mk M D R S H C P N => [M, D, R, S, H, C, P, N]

def typeCheckingMembershipTraceToEventFlow :
    TypeCheckingMembershipTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingMembershipTraceUp.mk M D R S H C P N =>
      [[BMark.b0],
        typeCheckingMembershipTraceEncodeBHist M,
        [BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingMembershipTraceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        typeCheckingMembershipTraceEncodeBHist N]

private def typeCheckingMembershipTraceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => typeCheckingMembershipTraceEventAtDefault index rest

def typeCheckingMembershipTraceFromEventFlow
    (ef : EventFlow) : Option TypeCheckingMembershipTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TypeCheckingMembershipTraceUp.mk
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 1 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 3 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 5 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 7 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 9 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 11 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 13 ef))
      (typeCheckingMembershipTraceDecodeBHist (typeCheckingMembershipTraceEventAtDefault 15 ef)))

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TypeCheckingMembershipTraceUp,
      typeCheckingMembershipTraceFromEventFlow
        (typeCheckingMembershipTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D R S H C P N =>
      change
        some
          (TypeCheckingMembershipTraceUp.mk
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist M))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist D))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist R))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist S))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist H))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist C))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist P))
            (typeCheckingMembershipTraceDecodeBHist
              (typeCheckingMembershipTraceEncodeBHist N))) =
          some (TypeCheckingMembershipTraceUp.mk M D R S H C P N)
      rw [TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode M,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode D,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode R,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode S,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode H,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode C,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode P,
        TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode N]

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_injective
    {x y : TypeCheckingMembershipTraceUp} :
    typeCheckingMembershipTraceToEventFlow x =
      typeCheckingMembershipTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeCheckingMembershipTraceFromEventFlow (typeCheckingMembershipTraceToEventFlow x) =
        typeCheckingMembershipTraceFromEventFlow (typeCheckingMembershipTraceToEventFlow y) :=
    congrArg typeCheckingMembershipTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_fields :
    ∀ x y : TypeCheckingMembershipTraceUp,
      typeCheckingMembershipTraceFields x = typeCheckingMembershipTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance typeCheckingMembershipTraceBHistCarrier :
    BHistCarrier TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeCheckingMembershipTraceToEventFlow
  fromEventFlow := typeCheckingMembershipTraceFromEventFlow

instance typeCheckingMembershipTraceChapterTasteGate :
    ChapterTasteGate TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typeCheckingMembershipTraceFromEventFlow
        (typeCheckingMembershipTraceToEventFlow x) = some x
    exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_injective heq)

instance typeCheckingMembershipTraceFieldFaithful :
    FieldFaithful TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := typeCheckingMembershipTraceFields
  field_faithful := TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_fields

instance typeCheckingMembershipTraceNontrivial :
    Nontrivial TypeCheckingMembershipTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypeCheckingMembershipTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypeCheckingMembershipTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TypeCheckingMembershipTraceMembership_row_nonescape
    {M D R S H C P N : BHist} (visibleM : M ≠ BHist.Empty) :
    typeCheckingMembershipTraceFields (TypeCheckingMembershipTraceUp.mk M D R S H C P N) ≠
      typeCheckingMembershipTraceFields
        (TypeCheckingMembershipTraceUp.mk BHist.Empty D R S H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  injection hfields with hM _tail
  exact visibleM hM

def taste_gate : ChapterTasteGate TypeCheckingMembershipTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typeCheckingMembershipTraceChapterTasteGate

theorem TypeCheckingMembershipTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      typeCheckingMembershipTraceDecodeBHist
        (typeCheckingMembershipTraceEncodeBHist h) = h) ∧
      (∀ x : TypeCheckingMembershipTraceUp,
        typeCheckingMembershipTraceFromEventFlow
          (typeCheckingMembershipTraceToEventFlow x) = some x) ∧
        (∀ x y : TypeCheckingMembershipTraceUp,
          typeCheckingMembershipTraceToEventFlow x =
            typeCheckingMembershipTraceToEventFlow y → x = y) ∧
          typeCheckingMembershipTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_injective heq
      · rfl

def TypeCheckingMembershipTraceKernelRows [AskSetup] (M D R S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle AskSetup
  Ext M BMark.b0 D ∧
    Cont D R C ∧
      SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty ∧
        hsame H H ∧ hsame P P ∧ hsame N N

theorem TypeCheckingMembershipTraceSubjectReduction_consumer_lock [AskSetup]
    {M D R S H C P N : BHist}
    (membership : Ext M BMark.b0 D)
    (route : Cont D R C)
    (readback : SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty) :
    TypeCheckingMembershipTraceKernelRows M D R S H C P N ∧
      typeCheckingMembershipTraceFields (TypeCheckingMembershipTraceUp.mk M D R S H C P N) =
        [M, D, R, S, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle AskSetup
  constructor
  · constructor
    · exact membership
    · constructor
      · exact route
      · constructor
        · exact readback
        · constructor
          · exact hsame_refl H
          · constructor
            · exact hsame_refl P
            · exact hsame_refl N
  · rfl

theorem TypeCheckingMembershipTraceClassifier_stability [AskSetup]
    {M D R S H C P N M' D' R' S' H' C' P' N' : BHist}
    (rows : TypeCheckingMembershipTraceKernelRows M D R S H C P N)
    (sameM : hsame M M')
    (sameD : hsame D D')
    (sameR : hsame R R')
    (sameS : hsame S S')
    (sameH : hsame H H')
    (sameC : hsame C C')
    (sameP : hsame P P')
    (sameN : hsame N N') :
    TypeCheckingMembershipTraceKernelRows M' D' R' S' H' C' P' N' ∧ hsame C C' := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle AskSetup
  cases sameM
  cases sameD
  cases sameR
  cases sameS
  cases sameH
  cases sameC
  cases sameP
  cases sameN
  cases rows with
  | intro membership rowsTail =>
      cases rowsTail with
      | intro route rowsTail =>
          cases rowsTail with
          | intro readback rowsTail =>
              cases rowsTail with
              | intro transportH rowsTail =>
                  cases rowsTail with
                  | intro transportP transportN =>
                      constructor
                      · constructor
                        · exact membership
                        · constructor
                          · exact route
                          · constructor
                            · exact readback
                            · constructor
                              · exact transportH
                              · constructor
                                · exact transportP
                                · exact transportN
                      · rfl

theorem TypeCheckingMembershipTraceNameCert_obligation_surface [AskSetup]
    {M D R S H C P N M' D' R' S' H' C' P' N' : BHist}
    (membership : Ext M BMark.b0 D)
    (route : Cont D R C)
    (readback : SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty)
    (sameM : hsame M M')
    (sameD : hsame D D')
    (sameR : hsame R R')
    (sameS : hsame S S')
    (sameH : hsame H H')
    (sameC : hsame C C')
    (sameP : hsame P P')
    (sameN : hsame N N') :
    Ext M' BMark.b0 D' ∧
      Cont D' R' C' ∧
        SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S' BHist.Empty ∧
          typeCheckingMembershipTraceFromEventFlow
              (typeCheckingMembershipTraceToEventFlow
                (TypeCheckingMembershipTraceUp.mk M D R S H C P N)) =
            some (TypeCheckingMembershipTraceUp.mk M D R S H C P N) ∧
            typeCheckingMembershipTraceFields
                (TypeCheckingMembershipTraceUp.mk M D R S H C P N) =
              [M, D, R, S, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle AskSetup
  cases sameM
  cases sameD
  cases sameR
  cases sameS
  cases sameH
  cases sameC
  cases sameP
  cases sameN
  constructor
  · exact membership
  · constructor
    · exact route
    · constructor
      · exact readback
      · constructor
        · exact
            TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip
              (TypeCheckingMembershipTraceUp.mk M D R S H C P N)
        · rfl

theorem TypeCheckingMembershipTraceRoute_coverage [AskSetup]
    {M D R S H C P N : BHist}
    (membership : Ext M BMark.b0 D)
    (route : Cont D R C)
    (readback : SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty) :
    Ext M BMark.b0 D ∧
      Cont D R C ∧
        SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty ∧
          typeCheckingMembershipTraceFields
              (TypeCheckingMembershipTraceUp.mk M D R S H C P N) =
            [M, D, R, S, H, C, P, N] ∧
            typeCheckingMembershipTraceFromEventFlow
                (typeCheckingMembershipTraceToEventFlow
                  (TypeCheckingMembershipTraceUp.mk M D R S H C P N)) =
              some (TypeCheckingMembershipTraceUp.mk M D R S H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle AskSetup
  constructor
  · exact membership
  · constructor
    · exact route
    · constructor
      · exact readback
      · constructor
        · rfl
        · exact
            TypeCheckingMembershipTraceTasteGate_single_carrier_alignment_round_trip
              (TypeCheckingMembershipTraceUp.mk M D R S H C P N)

theorem TypeCheckingMembershipTraceNameCert_obligations [AskSetup]
    {M D R S H C P N : BHist}
    (rows : TypeCheckingMembershipTraceKernelRows M D R S H C P N) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row M ∧ TypeCheckingMembershipTraceKernelRows M D R S H C P N)
      (fun row : BHist => hsame row M ∧ hsame D D ∧ hsame R R ∧ hsame S S)
      (fun row : BHist =>
        TypeCheckingMembershipTraceKernelRows M D R S H C P N ∧ hsame row M ∧
          hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N)
      hsame := by
  -- BEDC touchpoint anchor: BHist Ext Cont SigRel SemanticNameCert hsame
  exact {
    core := {
      carrier_inhabited := Exists.intro M ⟨hsame_refl M, rows⟩
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
        intro _row _other sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, hsame_refl D, hsame_refl R, hsame_refl S⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow with
      | intro sameRow kernelRows =>
          exact
            ⟨kernelRows, sameRow, hsame_refl H, hsame_refl C, hsame_refl P,
              hsame_refl N⟩
  }

theorem TypeCheckingMembershipTraceBridge_precondition [AskSetup]
    {M D R S H C P N : BHist}
    (membership : Ext M BMark.b0 D)
    (route : Cont D R C)
    (readback : SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty)
    (visibleR : R ≠ BHist.Empty) :
    TypeCheckingMembershipTraceKernelRows M D R S H C P N ∧
      typeCheckingMembershipTraceFields (TypeCheckingMembershipTraceUp.mk M D R S H C P N) =
        [M, D, R, S, H, C, P, N] ∧
        typeCheckingMembershipTraceFields (TypeCheckingMembershipTraceUp.mk M D R S H C P N) ≠
          typeCheckingMembershipTraceFields
            (TypeCheckingMembershipTraceUp.mk M D BHist.Empty S H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel ProbeBundle AskSetup
  constructor
  · exact
      (TypeCheckingMembershipTraceSubjectReduction_consumer_lock membership route readback).left
  · constructor
    · exact
        (TypeCheckingMembershipTraceSubjectReduction_consumer_lock membership route readback).right
    · intro hfields
      injection hfields with _ tail1
      injection tail1 with _ tail2
      injection tail2 with hR _
      exact visibleR hR

theorem TypeCheckingMembershipTrace_scoped_kernel_surface [AskSetup]
    {M D R S H C P N subjectReplay : BHist} :
    TypeCheckingMembershipTraceKernelRows M D R S H C P N →
      Cont R C subjectReplay →
        SemanticNameCert
          (fun row : BHist =>
            TypeCheckingMembershipTraceKernelRows M D R S H C P N ∧
              hsame row subjectReplay)
          (fun row : BHist =>
            Ext M BMark.b0 D ∧
              Cont D R C ∧
                Cont R C row ∧
                  SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty)
          (fun row : BHist =>
            hsame row subjectReplay ∧ hsame H H ∧ hsame P P ∧ hsame N N)
          hsame := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel SemanticNameCert hsame
  intro rows replay
  have rowsFull : TypeCheckingMembershipTraceKernelRows M D R S H C P N := rows
  obtain ⟨membership, derivation, readback, sameH, sameP, sameN⟩ := rows
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro subjectReplay (And.intro rowsFull (hsame_refl subjectReplay))
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
        intro _row _other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨membership, derivation, cont_result_hsame_transport replay (hsame_symm source.right),
          readback⟩
    ledger_sound := by
      intro row source
      exact ⟨source.right, sameH, sameP, sameN⟩
  }

theorem TypeCheckingMembershipTrace_obligation_assembly [AskSetup]
    {M D R S H C P N subjectReplay : BHist}
    (membership : Ext M BMark.b0 D)
    (route : Cont D R C)
    (readback : SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty)
    (replay : Cont R C subjectReplay)
    (visibleM : M != BHist.Empty)
    (visibleR : R != BHist.Empty) :
    SemanticNameCert
        (fun row : BHist =>
          TypeCheckingMembershipTraceKernelRows M D R S H C P N ∧
            hsame row subjectReplay)
        (fun row : BHist =>
          Ext M BMark.b0 D ∧ Cont D R C ∧ Cont R C row ∧
            SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) S BHist.Empty)
        (fun row : BHist =>
          hsame row subjectReplay ∧ hsame H H ∧ hsame P P ∧ hsame N N)
        hsame ∧
      typeCheckingMembershipTraceFields
          (TypeCheckingMembershipTraceUp.mk M D R S H C P N) ≠
        typeCheckingMembershipTraceFields
          (TypeCheckingMembershipTraceUp.mk BHist.Empty D R S H C P N) ∧
      typeCheckingMembershipTraceFields
          (TypeCheckingMembershipTraceUp.mk M D R S H C P N) ≠
        typeCheckingMembershipTraceFields
          (TypeCheckingMembershipTraceUp.mk M D BHist.Empty S H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont SigRel SemanticNameCert hsame
  have rows : TypeCheckingMembershipTraceKernelRows M D R S H C P N :=
    ⟨membership, route, readback, hsame_refl H, hsame_refl P, hsame_refl N⟩
  constructor
  · exact TypeCheckingMembershipTrace_scoped_kernel_surface rows replay
  · constructor
    · intro hfields
      injection hfields with hM _tail
      subst hM
      cases visibleM
    · intro hfields
      injection hfields with _ tail1
      injection tail1 with _ tail2
      injection tail2 with hR _
      subst hR
      cases visibleR

end BEDC.Derived.TypeCheckingMembershipTraceUp
