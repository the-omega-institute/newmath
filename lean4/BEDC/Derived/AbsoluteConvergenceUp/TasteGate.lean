import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbsoluteConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbsoluteConvergenceUp : Type where
  | mk (T M B U R E H C P N : BHist) : AbsoluteConvergenceUp
  deriving DecidableEq

def absoluteConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: absoluteConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: absoluteConvergenceEncodeBHist h

def absoluteConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (absoluteConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (absoluteConvergenceDecodeBHist tail)

private theorem absoluteConvergenceDecode_encode :
    ∀ h : BHist,
      absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def absoluteConvergenceFields : AbsoluteConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbsoluteConvergenceUp.mk T M B U R E H C P N => [T, M, B, U, R, E, H, C, P, N]

def absoluteConvergenceToEventFlow : AbsoluteConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (absoluteConvergenceFields x).map absoluteConvergenceEncodeBHist

private def absoluteConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => absoluteConvergenceEventAtDefault index rest

def absoluteConvergenceFromEventFlow (ef : EventFlow) : Option AbsoluteConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbsoluteConvergenceUp.mk
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 0 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 1 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 2 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 3 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 4 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 5 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 6 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 7 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 8 ef))
      (absoluteConvergenceDecodeBHist (absoluteConvergenceEventAtDefault 9 ef)))

private theorem absoluteConvergence_round_trip :
    ∀ x : AbsoluteConvergenceUp,
      absoluteConvergenceFromEventFlow (absoluteConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M B U R E H C P N =>
      change
        some
          (AbsoluteConvergenceUp.mk
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist T))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist M))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist B))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
            (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) =
          some (AbsoluteConvergenceUp.mk T M B U R E H C P N)
      have hT := absoluteConvergenceDecode_encode T
      have hM := absoluteConvergenceDecode_encode M
      have hB := absoluteConvergenceDecode_encode B
      have hU := absoluteConvergenceDecode_encode U
      have hR := absoluteConvergenceDecode_encode R
      have hE := absoluteConvergenceDecode_encode E
      have hH := absoluteConvergenceDecode_encode H
      have hC := absoluteConvergenceDecode_encode C
      have hP := absoluteConvergenceDecode_encode P
      have hN := absoluteConvergenceDecode_encode N
      exact congrArg some
        (calc
          AbsoluteConvergenceUp.mk
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist T))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist M))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist B))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) =
            AbsoluteConvergenceUp.mk T
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist M))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist B))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist M))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist B))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hT
          _ = AbsoluteConvergenceUp.mk T M
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist B))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist B))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hM
          _ = AbsoluteConvergenceUp.mk T M B
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T M z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist U))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hB
          _ = AbsoluteConvergenceUp.mk T M B U
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T M B z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist R))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hU
          _ = AbsoluteConvergenceUp.mk T M B U R
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T M B U z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist E))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hR
          _ = AbsoluteConvergenceUp.mk T M B U R E
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T M B U R z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist H))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hE
          _ = AbsoluteConvergenceUp.mk T M B U R E H
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T M B U R E z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist C))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hH
          _ = AbsoluteConvergenceUp.mk T M B U R E H C
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg
                  (fun z => AbsoluteConvergenceUp.mk T M B U R E H z
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist P))
                    (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hC
          _ = AbsoluteConvergenceUp.mk T M B U R E H C P
              (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N)) :=
                congrArg (fun z => AbsoluteConvergenceUp.mk T M B U R E H C z
                  (absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist N))) hP
          _ = AbsoluteConvergenceUp.mk T M B U R E H C P N :=
                congrArg (AbsoluteConvergenceUp.mk T M B U R E H C P) hN)

private theorem absoluteConvergenceToEventFlow_injective
    {x y : AbsoluteConvergenceUp} :
    absoluteConvergenceToEventFlow x = absoluteConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      absoluteConvergenceFromEventFlow (absoluteConvergenceToEventFlow x) =
        absoluteConvergenceFromEventFlow (absoluteConvergenceToEventFlow y) :=
    congrArg absoluteConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (absoluteConvergence_round_trip x).symm
      (Eq.trans hread (absoluteConvergence_round_trip y)))

instance absoluteConvergenceBHistCarrier :
    BHistCarrier AbsoluteConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := absoluteConvergenceToEventFlow
  fromEventFlow := absoluteConvergenceFromEventFlow

instance absoluteConvergenceChapterTasteGate :
    ChapterTasteGate AbsoluteConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change absoluteConvergenceFromEventFlow (absoluteConvergenceToEventFlow x) = some x
    exact absoluteConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (absoluteConvergenceToEventFlow_injective heq)

instance absoluteConvergenceFieldFaithful :
    FieldFaithful AbsoluteConvergenceUp where
  fields := absoluteConvergenceFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk T₁ M₁ B₁ U₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ M₂ B₂ U₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
        change [T₁, M₁, B₁, U₁, R₁, E₁, H₁, C₁, P₁, N₁] =
          [T₂, M₂, B₂, U₂, R₂, E₂, H₂, C₂, P₂, N₂] at h
        injection h with hT tail0
        injection tail0 with hM tail1
        injection tail1 with hB tail2
        injection tail2 with hU tail3
        injection tail3 with hR tail4
        injection tail4 with hE tail5
        injection tail5 with hH tail6
        injection tail6 with hC tail7
        injection tail7 with hP tail8
        injection tail8 with hN _
        subst hT
        subst hM
        subst hB
        subst hU
        subst hR
        subst hE
        subst hH
        subst hC
        subst hP
        subst hN
        rfl

instance absoluteConvergenceNontrivial :
    Nontrivial AbsoluteConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbsoluteConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AbsoluteConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AbsoluteConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, absoluteConvergenceDecodeBHist (absoluteConvergenceEncodeBHist h) = h) ∧
      (∀ x : AbsoluteConvergenceUp,
        absoluteConvergenceFromEventFlow (absoluteConvergenceToEventFlow x) = some x) ∧
      (∀ x y : AbsoluteConvergenceUp,
        absoluteConvergenceToEventFlow x = absoluteConvergenceToEventFlow y → x = y) ∧
      absoluteConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨absoluteConvergenceDecode_encode,
      absoluteConvergence_round_trip,
      fun _ _ heq => absoluteConvergenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AbsoluteConvergenceUp
