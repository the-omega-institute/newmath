import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotUp : Type where
  | mk (source pattern classifier stability ledger : BHist) : SternBrocotUp
  deriving DecidableEq

def sternBrocotEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotEncodeBHist h

def sternBrocotDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotDecodeBHist tail)

private theorem sternBrocot_decode_encode_bhist :
    ∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotFields : SternBrocotUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotUp.mk source pattern classifier stability ledger =>
      [source, pattern, classifier, stability, ledger]

def sternBrocotToEventFlow : SternBrocotUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sternBrocotFields x).map sternBrocotEncodeBHist

private def sternBrocotRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => sternBrocotRawAt n rest

def sternBrocotFromEventFlow : EventFlow → Option SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (SternBrocotUp.mk
        (sternBrocotDecodeBHist (sternBrocotRawAt 0 flow))
        (sternBrocotDecodeBHist (sternBrocotRawAt 1 flow))
        (sternBrocotDecodeBHist (sternBrocotRawAt 2 flow))
        (sternBrocotDecodeBHist (sternBrocotRawAt 3 flow))
        (sternBrocotDecodeBHist (sternBrocotRawAt 4 flow)))

private theorem sternBrocot_round_trip :
    ∀ x : SternBrocotUp,
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source pattern classifier stability ledger =>
      change
        some
          (SternBrocotUp.mk
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist source))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist pattern))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist classifier))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist stability))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist ledger))) =
          some (SternBrocotUp.mk source pattern classifier stability ledger)
      rw [sternBrocot_decode_encode_bhist source,
        sternBrocot_decode_encode_bhist pattern,
        sternBrocot_decode_encode_bhist classifier,
        sternBrocot_decode_encode_bhist stability,
        sternBrocot_decode_encode_bhist ledger]

private theorem sternBrocotToEventFlow_injective {x y : SternBrocotUp} :
    sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) =
        sternBrocotFromEventFlow (sternBrocotToEventFlow y) :=
    congrArg sternBrocotFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sternBrocot_round_trip x).symm
      (Eq.trans hread (sternBrocot_round_trip y)))

instance sternBrocotBHistCarrier : BHistCarrier SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotToEventFlow
  fromEventFlow := sternBrocotFromEventFlow

instance sternBrocotChapterTasteGate : ChapterTasteGate SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x
    exact sternBrocot_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sternBrocotToEventFlow_injective heq)

instance sternBrocotFieldFaithful : FieldFaithful SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sternBrocotFields
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ pattern₁ classifier₁ stability₁ ledger₁ =>
      cases y with
      | mk source₂ pattern₂ classifier₂ stability₂ ledger₂ =>
        simp only [sternBrocotFields] at h
        injection h with hsource tail₁
        injection tail₁ with hpattern tail₂
        injection tail₂ with hclassifier tail₃
        injection tail₃ with hstability tail₄
        injection tail₄ with hledger _
        cases hsource
        cases hpattern
        cases hclassifier
        cases hstability
        cases hledger
        rfl

instance sternBrocotNontrivial : Nontrivial SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SternBrocotUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SternBrocotUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sternBrocotChapterTasteGate

theorem SternBrocotTasteGate_single_carrier_alignment :
    (∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h) ∧
      (∀ x : SternBrocotUp,
        sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x) ∧
        (∀ x y : SternBrocotUp,
          sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y) ∧
          sternBrocotEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨sternBrocot_decode_encode_bhist,
      ⟨sternBrocot_round_trip,
        ⟨fun _ _ heq => sternBrocotToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.SternBrocotUp
