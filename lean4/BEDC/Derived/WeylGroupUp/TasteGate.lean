import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeylGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeylGroupUp : Type where
  | mk :
      (rootSource groupSource word action coxeter transport ledger endpoint : BHist) →
      WeylGroupUp
  deriving DecidableEq

def weylGroupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weylGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weylGroupEncodeBHist h

def weylGroupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weylGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weylGroupDecodeBHist tail)

private theorem WeylGroupTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, weylGroupDecodeBHist (weylGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weylGroupFields : WeylGroupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeylGroupUp.mk rootSource groupSource word action coxeter transport ledger endpoint =>
      [rootSource, groupSource, word, action, coxeter, transport, ledger, endpoint]

def weylGroupToEventFlow : WeylGroupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weylGroupFields x).map weylGroupEncodeBHist

def weylGroupFromEventFlow : EventFlow → Option WeylGroupUp
  -- BEDC touchpoint anchor: BHist BMark
  | rootSource :: groupSource :: word :: action :: coxeter :: transport :: ledger ::
      endpoint :: [] =>
      some
        (WeylGroupUp.mk
          (weylGroupDecodeBHist rootSource)
          (weylGroupDecodeBHist groupSource)
          (weylGroupDecodeBHist word)
          (weylGroupDecodeBHist action)
          (weylGroupDecodeBHist coxeter)
          (weylGroupDecodeBHist transport)
          (weylGroupDecodeBHist ledger)
          (weylGroupDecodeBHist endpoint))
  | _ => none

private theorem WeylGroupTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeylGroupUp, weylGroupFromEventFlow (weylGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rootSource groupSource word action coxeter transport ledger endpoint =>
      change
        some
          (WeylGroupUp.mk
            (weylGroupDecodeBHist (weylGroupEncodeBHist rootSource))
            (weylGroupDecodeBHist (weylGroupEncodeBHist groupSource))
            (weylGroupDecodeBHist (weylGroupEncodeBHist word))
            (weylGroupDecodeBHist (weylGroupEncodeBHist action))
            (weylGroupDecodeBHist (weylGroupEncodeBHist coxeter))
            (weylGroupDecodeBHist (weylGroupEncodeBHist transport))
            (weylGroupDecodeBHist (weylGroupEncodeBHist ledger))
            (weylGroupDecodeBHist (weylGroupEncodeBHist endpoint))) =
          some
            (WeylGroupUp.mk rootSource groupSource word action coxeter transport ledger
              endpoint)
      rw [WeylGroupTasteGate_single_carrier_alignment_decode_encode rootSource,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode groupSource,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode word,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode action,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode coxeter,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode transport,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode ledger,
        WeylGroupTasteGate_single_carrier_alignment_decode_encode endpoint]

private theorem WeylGroupTasteGate_single_carrier_alignment_injective {x y : WeylGroupUp} :
    weylGroupToEventFlow x = weylGroupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weylGroupFromEventFlow (weylGroupToEventFlow x) =
        weylGroupFromEventFlow (weylGroupToEventFlow y) :=
    congrArg weylGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WeylGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeylGroupTasteGate_single_carrier_alignment_round_trip y)))

private theorem WeylGroupTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : WeylGroupUp, weylGroupFields x = weylGroupFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk rootSource₁ groupSource₁ word₁ action₁ coxeter₁ transport₁ ledger₁ endpoint₁ =>
      cases y with
      | mk rootSource₂ groupSource₂ word₂ action₂ coxeter₂ transport₂ ledger₂ endpoint₂ =>
          injection h with hrootSource t1
          injection t1 with hgroupSource t2
          injection t2 with hword t3
          injection t3 with haction t4
          injection t4 with hcoxeter t5
          injection t5 with htransport t6
          injection t6 with hledger t7
          injection t7 with hendpoint _
          subst hrootSource
          subst hgroupSource
          subst hword
          subst haction
          subst hcoxeter
          subst htransport
          subst hledger
          subst hendpoint
          rfl

instance weylGroupBHistCarrier : BHistCarrier WeylGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weylGroupToEventFlow
  fromEventFlow := weylGroupFromEventFlow

instance weylGroupChapterTasteGate : ChapterTasteGate WeylGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weylGroupFromEventFlow (weylGroupToEventFlow x) = some x
    exact WeylGroupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeylGroupTasteGate_single_carrier_alignment_injective heq)

instance weylGroupFieldFaithful : FieldFaithful WeylGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := weylGroupFields
  field_faithful := WeylGroupTasteGate_single_carrier_alignment_field_faithful

instance weylGroupNontrivial : Nontrivial WeylGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WeylGroupUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      WeylGroupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WeylGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weylGroupChapterTasteGate

theorem WeylGroupTasteGate_single_carrier_alignment :
    (∀ h : BHist, weylGroupDecodeBHist (weylGroupEncodeBHist h) = h) ∧
      (∀ x : WeylGroupUp,
        weylGroupToEventFlow x = List.map weylGroupEncodeBHist (weylGroupFields x)) ∧
      (∀ x y : WeylGroupUp, weylGroupFields x = weylGroupFields y → x = y) ∧
      (∃ x y : WeylGroupUp, x ≠ y) ∧
      weylGroupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro WeylGroupTasteGate_single_carrier_alignment_decode_encode
      (And.intro
        (by
          intro x
          rfl)
        (And.intro WeylGroupTasteGate_single_carrier_alignment_field_faithful
          (And.intro
            (by
              exact
                ⟨WeylGroupUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty,
                  WeylGroupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                  by
                    intro h
                    cases h⟩)
            rfl)))

end BEDC.Derived.WeylGroupUp
