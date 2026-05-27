import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.UltrametricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive UltrametricSpaceUp : Type where
  | mk (M V T B E H K P N : BHist) : UltrametricSpaceUp
  deriving DecidableEq

def ultrametricSpaceFields : UltrametricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UltrametricSpaceUp.mk M V T B E H K P N => [M, V, T, B, E, H, K, P, N]

def ultrametricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ultrametricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ultrametricSpaceEncodeBHist h

def ultrametricSpaceToEventFlow : UltrametricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ultrametricSpaceFields x).map ultrametricSpaceEncodeBHist

private theorem UltrametricSpaceStrongTriangle_handoff_encode_display
    (h : BHist) :
    ∀ m, List.Mem m (ultrametricSpaceEncodeBHist h) →
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty =>
      intro m hm
      cases hm
  | e0 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inl rfl
      | tail _ hmTail =>
          exact ih m hmTail
  | e1 h ih =>
      intro m hm
      cases hm with
      | head =>
          exact Or.inr rfl
      | tail _ hmTail =>
          exact ih m hmTail

private theorem UltrametricSpaceStrongTriangle_handoff_flow_display
    (rows : List BHist) :
    ∀ w m, List.Mem w (rows.map ultrametricSpaceEncodeBHist) → List.Mem m w →
      m = BMark.b0 ∨ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  induction rows with
  | nil =>
      intro w m hw _hm
      cases hw
  | cons h rows ih =>
      intro w m hw hm
      cases hw with
      | head =>
          exact UltrametricSpaceStrongTriangle_handoff_encode_display h m hm
      | tail _ hwTail =>
          exact ih w m hwTail hm

theorem UltrametricSpaceStrongTriangle_handoff (x : UltrametricSpaceUp) :
    (∃ rows : List BHist, rows = ultrametricSpaceFields x) ∧
      (∀ w m, List.Mem w (ultrametricSpaceToEventFlow x) → List.Mem m w →
        m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨ultrametricSpaceFields x, rfl⟩
  · intro w m hw hm
    exact UltrametricSpaceStrongTriangle_handoff_flow_display
      (ultrametricSpaceFields x) w m hw hm

end BEDC.Derived.UltrametricSpaceUp
