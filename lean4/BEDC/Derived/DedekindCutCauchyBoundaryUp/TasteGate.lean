import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutCauchyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutCauchyBoundaryUp : Type where
  | mk (source pattern classifier stability ledger : BHist) :
      DedekindCutCauchyBoundaryUp
  deriving DecidableEq

def dedekindCutCauchyBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutCauchyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutCauchyBoundaryEncodeBHist h

def dedekindCutCauchyBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutCauchyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutCauchyBoundaryDecodeBHist tail)

private theorem dedekindCutCauchyBoundary_decode_encode_bhist :
    ∀ h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindCutCauchyBoundaryFields :
    DedekindCutCauchyBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutCauchyBoundaryUp.mk source pattern classifier stability ledger =>
      [source, pattern, classifier, stability, ledger]

def dedekindCutCauchyBoundaryToEventFlow :
    DedekindCutCauchyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (dedekindCutCauchyBoundaryFields x).map
        dedekindCutCauchyBoundaryEncodeBHist

private def dedekindCutCauchyBoundaryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => dedekindCutCauchyBoundaryRawAt n rest

def dedekindCutCauchyBoundaryFromEventFlow :
    EventFlow → Option DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (DedekindCutCauchyBoundaryUp.mk
        (dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryRawAt 0 flow))
        (dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryRawAt 1 flow))
        (dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryRawAt 2 flow))
        (dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryRawAt 3 flow))
        (dedekindCutCauchyBoundaryDecodeBHist
          (dedekindCutCauchyBoundaryRawAt 4 flow)))

private theorem dedekindCutCauchyBoundary_round_trip :
    ∀ x : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryFromEventFlow
        (dedekindCutCauchyBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source pattern classifier stability ledger =>
      change
        some
          (DedekindCutCauchyBoundaryUp.mk
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist source))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist pattern))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist classifier))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist stability))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist ledger))) =
          some
            (DedekindCutCauchyBoundaryUp.mk source pattern classifier stability
              ledger)
      rw [dedekindCutCauchyBoundary_decode_encode_bhist source,
        dedekindCutCauchyBoundary_decode_encode_bhist pattern,
        dedekindCutCauchyBoundary_decode_encode_bhist classifier,
        dedekindCutCauchyBoundary_decode_encode_bhist stability,
        dedekindCutCauchyBoundary_decode_encode_bhist ledger]

private theorem dedekindCutCauchyBoundaryToEventFlow_injective
    {x y : DedekindCutCauchyBoundaryUp} :
    dedekindCutCauchyBoundaryToEventFlow x =
        dedekindCutCauchyBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow y) :=
    congrArg dedekindCutCauchyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindCutCauchyBoundary_round_trip x).symm
      (Eq.trans hread (dedekindCutCauchyBoundary_round_trip y)))

instance dedekindCutCauchyBoundaryBHistCarrier :
    BHistCarrier DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutCauchyBoundaryToEventFlow
  fromEventFlow := dedekindCutCauchyBoundaryFromEventFlow

instance dedekindCutCauchyBoundaryChapterTasteGate :
    ChapterTasteGate DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCutCauchyBoundaryFromEventFlow
        (dedekindCutCauchyBoundaryToEventFlow x) = some x
    exact dedekindCutCauchyBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutCauchyBoundaryToEventFlow_injective heq)

instance dedekindCutCauchyBoundaryFieldFaithful :
    FieldFaithful DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindCutCauchyBoundaryFields
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ pattern₁ classifier₁ stability₁ ledger₁ =>
      cases y with
      | mk source₂ pattern₂ classifier₂ stability₂ ledger₂ =>
        simp only [dedekindCutCauchyBoundaryFields] at h
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

instance dedekindCutCauchyBoundaryNontrivial :
    Nontrivial DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindCutCauchyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DedekindCutCauchyBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutCauchyBoundaryChapterTasteGate

theorem DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist
        (dedekindCutCauchyBoundaryEncodeBHist h) = h) ∧
      (∀ x : DedekindCutCauchyBoundaryUp,
        dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) = some x) ∧
        (∀ x y : DedekindCutCauchyBoundaryUp,
          dedekindCutCauchyBoundaryToEventFlow x =
              dedekindCutCauchyBoundaryToEventFlow y →
            x = y) ∧
          dedekindCutCauchyBoundaryEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dedekindCutCauchyBoundary_decode_encode_bhist,
      ⟨dedekindCutCauchyBoundary_round_trip,
        ⟨fun _ _ heq => dedekindCutCauchyBoundaryToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.DedekindCutCauchyBoundaryUp
