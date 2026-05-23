import BEDC.Derived.GammaUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GammaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GammaUp : Type where
  | mk
      (domain pole apartness product modulus factorial recurrence holomorphic localName : BHist) :
      GammaUp
  deriving DecidableEq

def gammaTasteGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gammaTasteGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gammaTasteGateEncodeBHist h

def gammaTasteGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gammaTasteGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gammaTasteGateDecodeBHist tail)

private theorem GammaTasteGate_decode_encode :
    ∀ h : BHist, gammaTasteGateDecodeBHist (gammaTasteGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def GammaTasteGate_fields : GammaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GammaUp.mk domain pole apartness product modulus factorial recurrence holomorphic
      localName =>
      [domain, pole, apartness, product, modulus, factorial, recurrence, holomorphic,
        localName]

def gammaTasteGateToEventFlow : GammaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (GammaTasteGate_fields x).map gammaTasteGateEncodeBHist

def gammaTasteGateFromEventFlow : EventFlow → Option GammaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | domain :: pole :: apartness :: product :: modulus :: factorial :: recurrence ::
      holomorphic :: localName :: [] =>
      some
        (GammaUp.mk
          (gammaTasteGateDecodeBHist domain)
          (gammaTasteGateDecodeBHist pole)
          (gammaTasteGateDecodeBHist apartness)
          (gammaTasteGateDecodeBHist product)
          (gammaTasteGateDecodeBHist modulus)
          (gammaTasteGateDecodeBHist factorial)
          (gammaTasteGateDecodeBHist recurrence)
          (gammaTasteGateDecodeBHist holomorphic)
          (gammaTasteGateDecodeBHist localName))
  | _ => none

private theorem gammaTasteGate_round_trip :
    ∀ x : GammaUp, gammaTasteGateFromEventFlow (gammaTasteGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk domain pole apartness product modulus factorial recurrence holomorphic localName =>
      simp only [gammaTasteGateToEventFlow, GammaTasteGate_fields, gammaTasteGateFromEventFlow,
        List.map_cons, List.map_nil, GammaTasteGate_decode_encode]

private theorem gammaTasteGateToEventFlow_injective {x y : GammaUp} :
    gammaTasteGateToEventFlow x = gammaTasteGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = gammaTasteGateFromEventFlow (gammaTasteGateToEventFlow x) :=
        (gammaTasteGate_round_trip x).symm
      _ = gammaTasteGateFromEventFlow (gammaTasteGateToEventFlow y) :=
        congrArg gammaTasteGateFromEventFlow heq
      _ = some y := gammaTasteGate_round_trip y
  exact Option.some.inj optionEq

private theorem gammaTasteGate_field_faithful :
    ∀ x y : GammaUp, GammaTasteGate_fields x = GammaTasteGate_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk domain₁ pole₁ apartness₁ product₁ modulus₁ factorial₁ recurrence₁ holomorphic₁
      localName₁ =>
      cases y with
      | mk domain₂ pole₂ apartness₂ product₂ modulus₂ factorial₂ recurrence₂ holomorphic₂
          localName₂ =>
          cases h
          rfl

instance gammaTasteGateBHistCarrier : BHistCarrier GammaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gammaTasteGateToEventFlow
  fromEventFlow := gammaTasteGateFromEventFlow

instance gammaTasteGateChapterTasteGate : ChapterTasteGate GammaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gammaTasteGateFromEventFlow (gammaTasteGateToEventFlow x) = some x
    exact gammaTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gammaTasteGateToEventFlow_injective heq)

instance gammaTasteGateFieldFaithful : FieldFaithful GammaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := GammaTasteGate_fields
  field_faithful := gammaTasteGate_field_faithful

instance gammaTasteGateNontrivial : BEDC.Meta.TasteGate.Nontrivial GammaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GammaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      GammaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def gammaTasteGate : ChapterTasteGate GammaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gammaTasteGateChapterTasteGate

theorem GammaTasteGate_single_carrier_alignment :
    (∀ h : BHist, gammaTasteGateDecodeBHist (gammaTasteGateEncodeBHist h) = h) ∧
      GammaTasteGate_fields
          (GammaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨GammaTasteGate_decode_encode, rfl⟩

end BEDC.Derived.GammaUp
