import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofPatternClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofPatternClassifierUp : Type where
  | mk (w l d r e g h c q n : BHist) : ProofPatternClassifierUp
  deriving DecidableEq

def proofPatternClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofPatternClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofPatternClassifierEncodeBHist h

def proofPatternClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofPatternClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofPatternClassifierDecodeBHist tail)

private theorem proofPatternClassifier_decode_encode_bhist :
    ∀ h : BHist, proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def proofPatternClassifierToEventFlow : ProofPatternClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofPatternClassifierUp.mk w l d r e g h c q n =>
      [[BMark.b0],
        proofPatternClassifierEncodeBHist w,
        [BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist l,
        [BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist g,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        proofPatternClassifierEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist n]

private def proofPatternClassifierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => proofPatternClassifierEventAtDefault index rest

def proofPatternClassifierFromEventFlow (ef : EventFlow) : Option ProofPatternClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProofPatternClassifierUp.mk
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 1 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 3 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 5 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 7 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 9 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 11 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 13 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 15 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 17 ef))
      (proofPatternClassifierDecodeBHist (proofPatternClassifierEventAtDefault 19 ef)))

private theorem proofPatternClassifier_round_trip :
    ∀ x : ProofPatternClassifierUp,
      proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk w l d r e g h c q n =>
      change
        some
          (ProofPatternClassifierUp.mk
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist w))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist l))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist d))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist r))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist e))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist g))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist h))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist c))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist q))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist n))) =
          some (ProofPatternClassifierUp.mk w l d r e g h c q n)
      rw [proofPatternClassifier_decode_encode_bhist w,
        proofPatternClassifier_decode_encode_bhist l,
        proofPatternClassifier_decode_encode_bhist d,
        proofPatternClassifier_decode_encode_bhist r,
        proofPatternClassifier_decode_encode_bhist e,
        proofPatternClassifier_decode_encode_bhist g,
        proofPatternClassifier_decode_encode_bhist h,
        proofPatternClassifier_decode_encode_bhist c,
        proofPatternClassifier_decode_encode_bhist q,
        proofPatternClassifier_decode_encode_bhist n]

private theorem proofPatternClassifierToEventFlow_injective {x y : ProofPatternClassifierUp} :
    proofPatternClassifierToEventFlow x = proofPatternClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) =
        proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow y) :=
    congrArg proofPatternClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (proofPatternClassifier_round_trip x).symm
      (Eq.trans hread (proofPatternClassifier_round_trip y)))

private def proofPatternClassifierFields : ProofPatternClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProofPatternClassifierUp.mk w l d r e g h c q n => [w, l, d, r, e, g, h, c, q, n]

private theorem proofPatternClassifier_field_faithful :
    ∀ x y : ProofPatternClassifierUp,
      proofPatternClassifierFields x = proofPatternClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk w₁ l₁ d₁ r₁ e₁ g₁ h₁ c₁ q₁ n₁ =>
      cases y with
      | mk w₂ l₂ d₂ r₂ e₂ g₂ h₂ c₂ q₂ n₂ =>
          cases hfields
          rfl

instance proofPatternClassifierBHistCarrier : BHistCarrier ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofPatternClassifierToEventFlow
  fromEventFlow := proofPatternClassifierFromEventFlow

instance proofPatternClassifierChapterTasteGate : ChapterTasteGate ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) = some x
    exact proofPatternClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proofPatternClassifierToEventFlow_injective heq)

instance proofPatternClassifierFieldFaithful : FieldFaithful ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := proofPatternClassifierFields
  field_faithful := proofPatternClassifier_field_faithful

instance proofPatternClassifierNontrivial : Nontrivial ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProofPatternClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProofPatternClassifierUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProofPatternClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proofPatternClassifierChapterTasteGate

def taste_gate_witness : FieldFaithful ProofPatternClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proofPatternClassifierFieldFaithful

theorem ProofPatternClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist, proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist h) = h) ∧
      (∀ x : ProofPatternClassifierUp,
        proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) = some x) ∧
        (∀ x y : ProofPatternClassifierUp,
          proofPatternClassifierToEventFlow x = proofPatternClassifierToEventFlow y → x = y) ∧
          proofPatternClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨proofPatternClassifier_decode_encode_bhist,
      proofPatternClassifier_round_trip,
      (fun _ _ heq => proofPatternClassifierToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ProofPatternClassifierUp
