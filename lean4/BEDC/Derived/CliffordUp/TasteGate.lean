import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CliffordUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CliffordUp : Type where
  | mk : (unit vector product boundary endpoint : BHist) → CliffordUp
  deriving DecidableEq

def cliffordEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cliffordEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cliffordEncodeBHist h

def cliffordDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cliffordDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cliffordDecodeBHist tail)

private theorem CliffordTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cliffordDecodeBHist (cliffordEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cliffordFields : CliffordUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CliffordUp.mk unit vector product boundary endpoint =>
      [unit, vector, product, boundary, endpoint]

def cliffordToEventFlow : CliffordUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cliffordFields x).map cliffordEncodeBHist

def cliffordFromEventFlow : EventFlow → Option CliffordUp
  -- BEDC touchpoint anchor: BHist BMark
  | unit :: vector :: product :: boundary :: endpoint :: [] =>
      some
        (CliffordUp.mk
          (cliffordDecodeBHist unit)
          (cliffordDecodeBHist vector)
          (cliffordDecodeBHist product)
          (cliffordDecodeBHist boundary)
          (cliffordDecodeBHist endpoint))
  | _ => none

private theorem CliffordTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CliffordUp, cliffordFromEventFlow (cliffordToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk unit vector product boundary endpoint =>
      change
        some
          (CliffordUp.mk
            (cliffordDecodeBHist (cliffordEncodeBHist unit))
            (cliffordDecodeBHist (cliffordEncodeBHist vector))
            (cliffordDecodeBHist (cliffordEncodeBHist product))
            (cliffordDecodeBHist (cliffordEncodeBHist boundary))
            (cliffordDecodeBHist (cliffordEncodeBHist endpoint))) =
          some (CliffordUp.mk unit vector product boundary endpoint)
      rw [CliffordTasteGate_single_carrier_alignment_decode_encode unit,
        CliffordTasteGate_single_carrier_alignment_decode_encode vector,
        CliffordTasteGate_single_carrier_alignment_decode_encode product,
        CliffordTasteGate_single_carrier_alignment_decode_encode boundary,
        CliffordTasteGate_single_carrier_alignment_decode_encode endpoint]

private theorem CliffordTasteGate_single_carrier_alignment_injective {x y : CliffordUp} :
    cliffordToEventFlow x = cliffordToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cliffordFromEventFlow (cliffordToEventFlow x) =
        cliffordFromEventFlow (cliffordToEventFlow y) :=
    congrArg cliffordFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CliffordTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CliffordTasteGate_single_carrier_alignment_round_trip y)))

private theorem CliffordTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CliffordUp, cliffordFields x = cliffordFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk unit₁ vector₁ product₁ boundary₁ endpoint₁ =>
      cases y with
      | mk unit₂ vector₂ product₂ boundary₂ endpoint₂ =>
          injection h with hunit t1
          injection t1 with hvector t2
          injection t2 with hproduct t3
          injection t3 with hboundary t4
          injection t4 with hendpoint _
          subst hunit
          subst hvector
          subst hproduct
          subst hboundary
          subst hendpoint
          rfl

instance cliffordBHistCarrier : BHistCarrier CliffordUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cliffordToEventFlow
  fromEventFlow := cliffordFromEventFlow

instance cliffordChapterTasteGate : ChapterTasteGate CliffordUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cliffordFromEventFlow (cliffordToEventFlow x) = some x
    exact CliffordTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CliffordTasteGate_single_carrier_alignment_injective heq)

instance cliffordFieldFaithful : FieldFaithful CliffordUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cliffordFields
  field_faithful := CliffordTasteGate_single_carrier_alignment_field_faithful

instance cliffordNontrivial : Nontrivial CliffordUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CliffordUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CliffordUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CliffordUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cliffordChapterTasteGate

theorem CliffordTasteGate_single_carrier_alignment :
    (∀ h : BHist, cliffordDecodeBHist (cliffordEncodeBHist h) = h) ∧
      (∀ x : CliffordUp,
        cliffordToEventFlow x = List.map cliffordEncodeBHist (cliffordFields x)) ∧
      (∀ x y : CliffordUp, cliffordFields x = cliffordFields y → x = y) ∧
      (∃ x y : CliffordUp, x ≠ y) ∧
      cliffordEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro CliffordTasteGate_single_carrier_alignment_decode_encode
      (And.intro
        (by
          intro x
          rfl)
        (And.intro CliffordTasteGate_single_carrier_alignment_field_faithful
          (And.intro
            (by
              exact
                ⟨CliffordUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                  CliffordUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty,
                  by
                    intro h
                    cases h⟩)
            rfl)))

end BEDC.Derived.CliffordUp
