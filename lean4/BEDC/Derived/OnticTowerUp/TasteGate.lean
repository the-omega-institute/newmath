import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticTowerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticTowerUp : Type where
  | mk : (O A S R B L H C P N : BHist) → OnticTowerUp
  deriving DecidableEq

def onticTowerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticTowerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticTowerEncodeBHist h

def onticTowerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticTowerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticTowerDecodeBHist tail)

private theorem onticTowerDecode_encode_bhist :
    ∀ h : BHist, onticTowerDecodeBHist (onticTowerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def onticTowerFields : OnticTowerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticTowerUp.mk O A S R B L H C P N => [O, A, S, R, B, L, H, C, P, N]

def onticTowerToEventFlow : OnticTowerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map onticTowerEncodeBHist (onticTowerFields x)

def onticTowerFromEventFlow : EventFlow → Option OnticTowerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [O, A, S, R, B, L, H, C, P, N] =>
      some
        (OnticTowerUp.mk
          (onticTowerDecodeBHist O)
          (onticTowerDecodeBHist A)
          (onticTowerDecodeBHist S)
          (onticTowerDecodeBHist R)
          (onticTowerDecodeBHist B)
          (onticTowerDecodeBHist L)
          (onticTowerDecodeBHist H)
          (onticTowerDecodeBHist C)
          (onticTowerDecodeBHist P)
          (onticTowerDecodeBHist N))
  | _ => none

private theorem onticTower_round_trip :
    ∀ x : OnticTowerUp, onticTowerFromEventFlow (onticTowerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O A S R B L H C P N =>
      change
        some
          (OnticTowerUp.mk
            (onticTowerDecodeBHist (onticTowerEncodeBHist O))
            (onticTowerDecodeBHist (onticTowerEncodeBHist A))
            (onticTowerDecodeBHist (onticTowerEncodeBHist S))
            (onticTowerDecodeBHist (onticTowerEncodeBHist R))
            (onticTowerDecodeBHist (onticTowerEncodeBHist B))
            (onticTowerDecodeBHist (onticTowerEncodeBHist L))
            (onticTowerDecodeBHist (onticTowerEncodeBHist H))
            (onticTowerDecodeBHist (onticTowerEncodeBHist C))
            (onticTowerDecodeBHist (onticTowerEncodeBHist P))
            (onticTowerDecodeBHist (onticTowerEncodeBHist N))) =
          some (OnticTowerUp.mk O A S R B L H C P N)
      rw [onticTowerDecode_encode_bhist O, onticTowerDecode_encode_bhist A,
        onticTowerDecode_encode_bhist S, onticTowerDecode_encode_bhist R,
        onticTowerDecode_encode_bhist B, onticTowerDecode_encode_bhist L,
        onticTowerDecode_encode_bhist H, onticTowerDecode_encode_bhist C,
        onticTowerDecode_encode_bhist P, onticTowerDecode_encode_bhist N]

private theorem onticTowerToEventFlow_injective {x y : OnticTowerUp} :
    onticTowerToEventFlow x = onticTowerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticTowerFromEventFlow (onticTowerToEventFlow x) =
        onticTowerFromEventFlow (onticTowerToEventFlow y) :=
    congrArg onticTowerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticTower_round_trip x).symm (Eq.trans hread (onticTower_round_trip y)))

private theorem onticTower_field_faithful :
    ∀ x y : OnticTowerUp, onticTowerFields x = onticTowerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk O₁ A₁ S₁ R₁ B₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ A₂ S₂ R₂ B₂ L₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance onticTowerBHistCarrier : BHistCarrier OnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticTowerToEventFlow
  fromEventFlow := onticTowerFromEventFlow

instance onticTowerChapterTasteGate : ChapterTasteGate OnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticTowerFromEventFlow (onticTowerToEventFlow x) = some x
    exact onticTower_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticTowerToEventFlow_injective heq)

instance onticTowerFieldFaithful : FieldFaithful OnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := onticTowerFields
  field_faithful := onticTower_field_faithful

instance onticTowerNontrivial : Nontrivial OnticTowerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticTowerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OnticTowerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OnticTowerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onticTowerChapterTasteGate

theorem OnticTowerTasteGate_single_carrier_alignment :
    (∀ h : BHist, onticTowerDecodeBHist (onticTowerEncodeBHist h) = h) ∧
      (∀ x : OnticTowerUp,
        onticTowerToEventFlow x =
          List.map onticTowerEncodeBHist (onticTowerFields x)) ∧
        (∀ x y : OnticTowerUp, onticTowerFields x = onticTowerFields y → x = y) ∧
          (∃ x y : OnticTowerUp, x ≠ y) ∧
            onticTowerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact onticTowerDecode_encode_bhist
  constructor
  · intro x
    cases x
    rfl
  constructor
  · exact onticTower_field_faithful
  constructor
  · exact
      ⟨OnticTowerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        OnticTowerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩
  · rfl

end BEDC.Derived.OnticTowerUp
