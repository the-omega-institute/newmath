import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoobSurvivalChainUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoobSurvivalChainUp : Type where
  | mk (K V T Pi D H C P N : BHist) : DoobSurvivalChainUp
  deriving DecidableEq

def doobSurvivalChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doobSurvivalChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doobSurvivalChainEncodeBHist h

def doobSurvivalChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doobSurvivalChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doobSurvivalChainDecodeBHist tail)

private theorem doobSurvivalChainDecodeEncodeBHist :
    ∀ h : BHist, doobSurvivalChainDecodeBHist (doobSurvivalChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def doobSurvivalChainFields : DoobSurvivalChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoobSurvivalChainUp.mk K V T Pi D H C P N => [K, V, T, Pi, D, H, C, P, N]

def doobSurvivalChainToEventFlow : DoobSurvivalChainUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (doobSurvivalChainFields x).map doobSurvivalChainEncodeBHist

def doobSurvivalChainFromEventFlow : EventFlow → Option DoobSurvivalChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | K :: V :: T :: Pi :: D :: H :: C :: P :: N :: [] =>
      some
        (DoobSurvivalChainUp.mk
          (doobSurvivalChainDecodeBHist K)
          (doobSurvivalChainDecodeBHist V)
          (doobSurvivalChainDecodeBHist T)
          (doobSurvivalChainDecodeBHist Pi)
          (doobSurvivalChainDecodeBHist D)
          (doobSurvivalChainDecodeBHist H)
          (doobSurvivalChainDecodeBHist C)
          (doobSurvivalChainDecodeBHist P)
          (doobSurvivalChainDecodeBHist N))
  | _ => none

private theorem doobSurvivalChainRoundTrip :
    ∀ x : DoobSurvivalChainUp,
      doobSurvivalChainFromEventFlow (doobSurvivalChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K V T Pi D H C P N =>
      simp only [doobSurvivalChainToEventFlow, doobSurvivalChainFields,
        doobSurvivalChainFromEventFlow, List.map_cons, List.map_nil,
        doobSurvivalChainDecodeEncodeBHist]

private theorem doobSurvivalChainToEventFlow_injective
    {x y : DoobSurvivalChainUp} :
    doobSurvivalChainToEventFlow x = doobSurvivalChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doobSurvivalChainFromEventFlow (doobSurvivalChainToEventFlow x) =
        doobSurvivalChainFromEventFlow (doobSurvivalChainToEventFlow y) :=
    congrArg doobSurvivalChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (doobSurvivalChainRoundTrip x).symm
      (Eq.trans hread (doobSurvivalChainRoundTrip y)))

private theorem doobSurvivalChainFieldsFaithful :
    ∀ x y : DoobSurvivalChainUp, doobSurvivalChainFields x = doobSurvivalChainFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ V₁ T₁ Pi₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ V₂ T₂ Pi₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance doobSurvivalChainBHistCarrier : BHistCarrier DoobSurvivalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doobSurvivalChainToEventFlow
  fromEventFlow := doobSurvivalChainFromEventFlow

instance doobSurvivalChainChapterTasteGate :
    ChapterTasteGate DoobSurvivalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doobSurvivalChainFromEventFlow (doobSurvivalChainToEventFlow x) = some x
    exact doobSurvivalChainRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (doobSurvivalChainToEventFlow_injective heq)

instance doobSurvivalChainFieldFaithful :
    FieldFaithful DoobSurvivalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := doobSurvivalChainFields
  field_faithful := doobSurvivalChainFieldsFaithful

instance doobSurvivalChainNontrivial : Nontrivial DoobSurvivalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DoobSurvivalChainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DoobSurvivalChainUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DoobSurvivalChainTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DoobSurvivalChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  doobSurvivalChainChapterTasteGate

theorem DoobSurvivalChainTasteGate_single_carrier_alignment :
    (forall K V T Pi D H C P N : BHist,
      doobSurvivalChainFields (DoobSurvivalChainUp.mk K V T Pi D H C P N) =
        [K, V, T, Pi, D, H, C, P, N]) ∧
      doobSurvivalChainEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.DoobSurvivalChainUp.TasteGate
