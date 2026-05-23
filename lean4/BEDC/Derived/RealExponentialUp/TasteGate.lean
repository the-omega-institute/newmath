import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealExponentialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealExponentialUp : Type where
  | mk (A F B U M K P S R Q T C L N : BHist) : RealExponentialUp
  deriving DecidableEq

def realExponentialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realExponentialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realExponentialEncodeBHist h

def realExponentialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realExponentialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realExponentialDecodeBHist tail)

private theorem realExponentialDecode_encode :
    ∀ h : BHist, realExponentialDecodeBHist (realExponentialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realExponentialFields : RealExponentialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealExponentialUp.mk A F B U M K P S R Q T C L N => [A, F, B, U, M, K, P, S, R, Q, T, C, L, N]

def realExponentialToEventFlow : RealExponentialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realExponentialFields x).map realExponentialEncodeBHist

private def realExponentialEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realExponentialEventAtDefault index rest

def realExponentialFromEventFlow (ef : EventFlow) : Option RealExponentialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealExponentialUp.mk
      (realExponentialDecodeBHist (realExponentialEventAtDefault 0 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 1 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 2 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 3 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 4 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 5 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 6 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 7 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 8 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 9 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 10 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 11 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 12 ef))
      (realExponentialDecodeBHist (realExponentialEventAtDefault 13 ef)))

private theorem realExponential_round_trip :
    ∀ x : RealExponentialUp,
      realExponentialFromEventFlow (realExponentialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A F B U M K P S R Q T C L N =>
      change
        some
          (RealExponentialUp.mk
            (realExponentialDecodeBHist (realExponentialEncodeBHist A))
            (realExponentialDecodeBHist (realExponentialEncodeBHist F))
            (realExponentialDecodeBHist (realExponentialEncodeBHist B))
            (realExponentialDecodeBHist (realExponentialEncodeBHist U))
            (realExponentialDecodeBHist (realExponentialEncodeBHist M))
            (realExponentialDecodeBHist (realExponentialEncodeBHist K))
            (realExponentialDecodeBHist (realExponentialEncodeBHist P))
            (realExponentialDecodeBHist (realExponentialEncodeBHist S))
            (realExponentialDecodeBHist (realExponentialEncodeBHist R))
            (realExponentialDecodeBHist (realExponentialEncodeBHist Q))
            (realExponentialDecodeBHist (realExponentialEncodeBHist T))
            (realExponentialDecodeBHist (realExponentialEncodeBHist C))
            (realExponentialDecodeBHist (realExponentialEncodeBHist L))
            (realExponentialDecodeBHist (realExponentialEncodeBHist N))) =
          some (RealExponentialUp.mk A F B U M K P S R Q T C L N)
      rw [realExponentialDecode_encode A, realExponentialDecode_encode F,
        realExponentialDecode_encode B, realExponentialDecode_encode U,
        realExponentialDecode_encode M, realExponentialDecode_encode K,
        realExponentialDecode_encode P, realExponentialDecode_encode S,
        realExponentialDecode_encode R, realExponentialDecode_encode Q,
        realExponentialDecode_encode T, realExponentialDecode_encode C,
        realExponentialDecode_encode L, realExponentialDecode_encode N]

private theorem realExponentialToEventFlow_injective {x y : RealExponentialUp} :
    realExponentialToEventFlow x = realExponentialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realExponentialFromEventFlow (realExponentialToEventFlow x) =
        realExponentialFromEventFlow (realExponentialToEventFlow y) :=
    congrArg realExponentialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realExponential_round_trip x).symm
      (Eq.trans hread (realExponential_round_trip y)))

instance realExponentialBHistCarrier :
    BHistCarrier RealExponentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realExponentialToEventFlow
  fromEventFlow := realExponentialFromEventFlow

instance realExponentialChapterTasteGate :
    ChapterTasteGate RealExponentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realExponentialFromEventFlow (realExponentialToEventFlow x) = some x
    exact realExponential_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realExponentialToEventFlow_injective heq)

instance realExponentialFieldFaithful :
    FieldFaithful RealExponentialUp where
  fields := realExponentialFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk A₁ F₁ B₁ U₁ M₁ K₁ P₁ S₁ R₁ Q₁ T₁ C₁ L₁ N₁ =>
      cases y with
      | mk A₂ F₂ B₂ U₂ M₂ K₂ P₂ S₂ R₂ Q₂ T₂ C₂ L₂ N₂ =>
        change [A₁, F₁, B₁, U₁, M₁, K₁, P₁, S₁, R₁, Q₁, T₁, C₁, L₁, N₁] =
          [A₂, F₂, B₂, U₂, M₂, K₂, P₂, S₂, R₂, Q₂, T₂, C₂, L₂, N₂] at h
        injection h with hA tail0
        injection tail0 with hF tail1
        injection tail1 with hB tail2
        injection tail2 with hU tail3
        injection tail3 with hM tail4
        injection tail4 with hK tail5
        injection tail5 with hP tail6
        injection tail6 with hS tail7
        injection tail7 with hR tail8
        injection tail8 with hQ tail9
        injection tail9 with hT tail10
        injection tail10 with hC tail11
        injection tail11 with hL tail12
        injection tail12 with hN _
        subst hA
        subst hF
        subst hB
        subst hU
        subst hM
        subst hK
        subst hP
        subst hS
        subst hR
        subst hQ
        subst hT
        subst hC
        subst hL
        subst hN
        rfl

instance realExponentialNontrivial :
    Nontrivial RealExponentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealExponentialUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealExponentialUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealExponentialTasteGate_single_carrier_alignment :
    (∀ h : BHist, realExponentialDecodeBHist (realExponentialEncodeBHist h) = h) ∧
      (∀ x : RealExponentialUp,
        realExponentialFromEventFlow (realExponentialToEventFlow x) = some x) ∧
      (∀ x y : RealExponentialUp,
        realExponentialToEventFlow x = realExponentialToEventFlow y → x = y) ∧
      realExponentialEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realExponentialDecode_encode,
      realExponential_round_trip,
      fun _ _ heq => realExponentialToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealExponentialUp
