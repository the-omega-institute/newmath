import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlexanderDualTriggerAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlexanderDualTriggerAlgebraUp : Type where
  | mk (B T I U L R H C P N : BHist) : AlexanderDualTriggerAlgebraUp
  deriving DecidableEq

def alexanderDualTriggerAlgebraEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: alexanderDualTriggerAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: alexanderDualTriggerAlgebraEncodeBHist h

def alexanderDualTriggerAlgebraDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (alexanderDualTriggerAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (alexanderDualTriggerAlgebraDecodeBHist tail)

private theorem alexanderDualTriggerAlgebraDecode_encode :
    ∀ h : BHist,
      alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def alexanderDualTriggerAlgebraFields :
    AlexanderDualTriggerAlgebraUp → List BHist
  | AlexanderDualTriggerAlgebraUp.mk B T I U L R H C P N =>
      [B, T, I, U, L, R, H, C, P, N]

def alexanderDualTriggerAlgebraToEventFlow :
    AlexanderDualTriggerAlgebraUp → EventFlow
  | x =>
      (alexanderDualTriggerAlgebraFields x).map
        alexanderDualTriggerAlgebraEncodeBHist

private def alexanderDualTriggerAlgebraEventAtDefault : Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      alexanderDualTriggerAlgebraEventAtDefault index rest

def alexanderDualTriggerAlgebraFromEventFlow
    (ef : EventFlow) : Option AlexanderDualTriggerAlgebraUp :=
  some
    (AlexanderDualTriggerAlgebraUp.mk
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 0 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 1 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 2 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 3 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 4 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 5 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 6 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 7 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 8 ef))
      (alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEventAtDefault 9 ef)))

private theorem alexanderDualTriggerAlgebra_round_trip :
    ∀ x : AlexanderDualTriggerAlgebraUp,
      alexanderDualTriggerAlgebraFromEventFlow
        (alexanderDualTriggerAlgebraToEventFlow x) = some x := by
  intro x
  cases x with
  | mk B T I U L R H C P N =>
      change
        some
          (AlexanderDualTriggerAlgebraUp.mk
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist B))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist T))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist I))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist U))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist L))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist R))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist H))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist C))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist P))
            (alexanderDualTriggerAlgebraDecodeBHist
              (alexanderDualTriggerAlgebraEncodeBHist N))) =
          some (AlexanderDualTriggerAlgebraUp.mk B T I U L R H C P N)
      rw [alexanderDualTriggerAlgebraDecode_encode B,
        alexanderDualTriggerAlgebraDecode_encode T,
        alexanderDualTriggerAlgebraDecode_encode I,
        alexanderDualTriggerAlgebraDecode_encode U,
        alexanderDualTriggerAlgebraDecode_encode L,
        alexanderDualTriggerAlgebraDecode_encode R,
        alexanderDualTriggerAlgebraDecode_encode H,
        alexanderDualTriggerAlgebraDecode_encode C,
        alexanderDualTriggerAlgebraDecode_encode P,
        alexanderDualTriggerAlgebraDecode_encode N]

private theorem alexanderDualTriggerAlgebraToEventFlow_injective
    {x y : AlexanderDualTriggerAlgebraUp} :
    alexanderDualTriggerAlgebraToEventFlow x =
      alexanderDualTriggerAlgebraToEventFlow y → x = y := by
  intro heq
  have hread :
      alexanderDualTriggerAlgebraFromEventFlow
          (alexanderDualTriggerAlgebraToEventFlow x) =
        alexanderDualTriggerAlgebraFromEventFlow
          (alexanderDualTriggerAlgebraToEventFlow y) :=
    congrArg alexanderDualTriggerAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (alexanderDualTriggerAlgebra_round_trip x).symm
      (Eq.trans hread (alexanderDualTriggerAlgebra_round_trip y)))

instance alexanderDualTriggerAlgebraBHistCarrier :
    BHistCarrier AlexanderDualTriggerAlgebraUp where
  toEventFlow := alexanderDualTriggerAlgebraToEventFlow
  fromEventFlow := alexanderDualTriggerAlgebraFromEventFlow

instance alexanderDualTriggerAlgebraChapterTasteGate :
    ChapterTasteGate AlexanderDualTriggerAlgebraUp where
  round_trip := by
    intro x
    change
      alexanderDualTriggerAlgebraFromEventFlow
        (alexanderDualTriggerAlgebraToEventFlow x) = some x
    exact alexanderDualTriggerAlgebra_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (alexanderDualTriggerAlgebraToEventFlow_injective heq)

instance alexanderDualTriggerAlgebraFieldFaithful :
    FieldFaithful AlexanderDualTriggerAlgebraUp where
  fields := alexanderDualTriggerAlgebraFields
  field_faithful := by
    intro x y h
    cases x with
    | mk B₁ T₁ I₁ U₁ L₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ T₂ I₂ U₂ L₂ R₂ H₂ C₂ P₂ N₂ =>
        change [B₁, T₁, I₁, U₁, L₁, R₁, H₁, C₁, P₁, N₁] =
          [B₂, T₂, I₂, U₂, L₂, R₂, H₂, C₂, P₂, N₂] at h
        injection h with hB tail0
        injection tail0 with hT tail1
        injection tail1 with hI tail2
        injection tail2 with hU tail3
        injection tail3 with hL tail4
        injection tail4 with hR tail5
        injection tail5 with hH tail6
        injection tail6 with hC tail7
        injection tail7 with hP tail8
        injection tail8 with hN _
        subst hB
        subst hT
        subst hI
        subst hU
        subst hL
        subst hR
        subst hH
        subst hC
        subst hP
        subst hN
        rfl

instance alexanderDualTriggerAlgebraNontrivial :
    Nontrivial AlexanderDualTriggerAlgebraUp where
  witness_pair :=
    ⟨AlexanderDualTriggerAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AlexanderDualTriggerAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AlexanderDualTriggerAlgebraTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      alexanderDualTriggerAlgebraDecodeBHist
        (alexanderDualTriggerAlgebraEncodeBHist h) = h) ∧
      (∀ x : AlexanderDualTriggerAlgebraUp,
        alexanderDualTriggerAlgebraFromEventFlow
          (alexanderDualTriggerAlgebraToEventFlow x) = some x) ∧
      (∀ x y : AlexanderDualTriggerAlgebraUp,
        alexanderDualTriggerAlgebraToEventFlow x =
          alexanderDualTriggerAlgebraToEventFlow y → x = y) ∧
      alexanderDualTriggerAlgebraEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact
    ⟨alexanderDualTriggerAlgebraDecode_encode,
      alexanderDualTriggerAlgebra_round_trip,
      fun _ _ heq => alexanderDualTriggerAlgebraToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AlexanderDualTriggerAlgebraUp
