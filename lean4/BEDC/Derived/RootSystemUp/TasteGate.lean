import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RootSystemUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RootSystemUp : Type where
  | mk :
      (support vectorClassifier rootCarrier rootClassifier nonzero reflection cartan
        stability ledger source : BHist) → RootSystemUp
  deriving DecidableEq

def rootSystemEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rootSystemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rootSystemEncodeBHist h

def rootSystemDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rootSystemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rootSystemDecodeBHist tail)

private theorem RootSystemTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rootSystemDecodeBHist (rootSystemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rootSystemFields : RootSystemUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RootSystemUp.mk support vectorClassifier rootCarrier rootClassifier nonzero reflection
      cartan stability ledger source =>
      [support, vectorClassifier, rootCarrier, rootClassifier, nonzero, reflection, cartan,
        stability, ledger, source]

def rootSystemToEventFlow : RootSystemUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rootSystemFields x).map rootSystemEncodeBHist

def rootSystemFromEventFlow : EventFlow → Option RootSystemUp
  -- BEDC touchpoint anchor: BHist BMark
  | support :: vectorClassifier :: rootCarrier :: rootClassifier :: nonzero :: reflection ::
      cartan :: stability :: ledger :: source :: [] =>
      some
        (RootSystemUp.mk
          (rootSystemDecodeBHist support)
          (rootSystemDecodeBHist vectorClassifier)
          (rootSystemDecodeBHist rootCarrier)
          (rootSystemDecodeBHist rootClassifier)
          (rootSystemDecodeBHist nonzero)
          (rootSystemDecodeBHist reflection)
          (rootSystemDecodeBHist cartan)
          (rootSystemDecodeBHist stability)
          (rootSystemDecodeBHist ledger)
          (rootSystemDecodeBHist source))
  | _ => none

private theorem RootSystemTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RootSystemUp, rootSystemFromEventFlow (rootSystemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk support vectorClassifier rootCarrier rootClassifier nonzero reflection cartan stability
      ledger source =>
      change
        some
          (RootSystemUp.mk
            (rootSystemDecodeBHist (rootSystemEncodeBHist support))
            (rootSystemDecodeBHist (rootSystemEncodeBHist vectorClassifier))
            (rootSystemDecodeBHist (rootSystemEncodeBHist rootCarrier))
            (rootSystemDecodeBHist (rootSystemEncodeBHist rootClassifier))
            (rootSystemDecodeBHist (rootSystemEncodeBHist nonzero))
            (rootSystemDecodeBHist (rootSystemEncodeBHist reflection))
            (rootSystemDecodeBHist (rootSystemEncodeBHist cartan))
            (rootSystemDecodeBHist (rootSystemEncodeBHist stability))
            (rootSystemDecodeBHist (rootSystemEncodeBHist ledger))
            (rootSystemDecodeBHist (rootSystemEncodeBHist source))) =
          some
            (RootSystemUp.mk support vectorClassifier rootCarrier rootClassifier nonzero
              reflection cartan stability ledger source)
      rw [RootSystemTasteGate_single_carrier_alignment_decode_encode support,
        RootSystemTasteGate_single_carrier_alignment_decode_encode vectorClassifier,
        RootSystemTasteGate_single_carrier_alignment_decode_encode rootCarrier,
        RootSystemTasteGate_single_carrier_alignment_decode_encode rootClassifier,
        RootSystemTasteGate_single_carrier_alignment_decode_encode nonzero,
        RootSystemTasteGate_single_carrier_alignment_decode_encode reflection,
        RootSystemTasteGate_single_carrier_alignment_decode_encode cartan,
        RootSystemTasteGate_single_carrier_alignment_decode_encode stability,
        RootSystemTasteGate_single_carrier_alignment_decode_encode ledger,
        RootSystemTasteGate_single_carrier_alignment_decode_encode source]

private theorem RootSystemTasteGate_single_carrier_alignment_injective {x y : RootSystemUp} :
    rootSystemToEventFlow x = rootSystemToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rootSystemFromEventFlow (rootSystemToEventFlow x) =
        rootSystemFromEventFlow (rootSystemToEventFlow y) :=
    congrArg rootSystemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RootSystemTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RootSystemTasteGate_single_carrier_alignment_round_trip y)))

private theorem RootSystemTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RootSystemUp, rootSystemFields x = rootSystemFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk support₁ vectorClassifier₁ rootCarrier₁ rootClassifier₁ nonzero₁ reflection₁
      cartan₁ stability₁ ledger₁ source₁ =>
      cases y with
      | mk support₂ vectorClassifier₂ rootCarrier₂ rootClassifier₂ nonzero₂ reflection₂
          cartan₂ stability₂ ledger₂ source₂ =>
          injection h with hsupport t1
          injection t1 with hvectorClassifier t2
          injection t2 with hrootCarrier t3
          injection t3 with hrootClassifier t4
          injection t4 with hnonzero t5
          injection t5 with hreflection t6
          injection t6 with hcartan t7
          injection t7 with hstability t8
          injection t8 with hledger t9
          injection t9 with hsource _
          subst hsupport
          subst hvectorClassifier
          subst hrootCarrier
          subst hrootClassifier
          subst hnonzero
          subst hreflection
          subst hcartan
          subst hstability
          subst hledger
          subst hsource
          rfl

instance rootSystemBHistCarrier : BHistCarrier RootSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rootSystemToEventFlow
  fromEventFlow := rootSystemFromEventFlow

instance rootSystemChapterTasteGate : ChapterTasteGate RootSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rootSystemFromEventFlow (rootSystemToEventFlow x) = some x
    exact RootSystemTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RootSystemTasteGate_single_carrier_alignment_injective heq)

instance rootSystemFieldFaithful : FieldFaithful RootSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rootSystemFields
  field_faithful := RootSystemTasteGate_single_carrier_alignment_field_faithful

instance rootSystemNontrivial : Nontrivial RootSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RootSystemUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RootSystemUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RootSystemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rootSystemChapterTasteGate

theorem RootSystemTasteGate_single_carrier_alignment :
    (∀ h : BHist, rootSystemDecodeBHist (rootSystemEncodeBHist h) = h) ∧
      (∀ x : RootSystemUp,
        rootSystemToEventFlow x = List.map rootSystemEncodeBHist (rootSystemFields x)) ∧
      (∀ x y : RootSystemUp, rootSystemFields x = rootSystemFields y → x = y) ∧
      (∃ x y : RootSystemUp, x ≠ y) ∧
      rootSystemEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro RootSystemTasteGate_single_carrier_alignment_decode_encode
      (And.intro
        (by
          intro x
          rfl)
        (And.intro RootSystemTasteGate_single_carrier_alignment_field_faithful
          (And.intro
            (by
              exact
                ⟨RootSystemUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                  RootSystemUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                  by
                    intro h
                    cases h⟩)
            rfl)))

end BEDC.Derived.RootSystemUp
