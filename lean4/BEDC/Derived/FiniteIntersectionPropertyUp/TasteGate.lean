import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteIntersectionPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteIntersectionPropertyUp : Type where
  | mk
      (index closedFamily acceptance closedIntervalCompletion nestedWindow cantorHandoff
        finiteNetWitness realSeal transport replay provenance nameCert : BHist) :
      FiniteIntersectionPropertyUp
  deriving DecidableEq

def finiteIntersectionPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteIntersectionPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteIntersectionPropertyEncodeBHist h

def finiteIntersectionPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteIntersectionPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteIntersectionPropertyDecodeBHist tail)

private theorem FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteIntersectionPropertyFields :
    FiniteIntersectionPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteIntersectionPropertyUp.mk index closedFamily acceptance
      closedIntervalCompletion nestedWindow cantorHandoff finiteNetWitness realSeal
      transport replay provenance nameCert =>
      [index, closedFamily, acceptance, closedIntervalCompletion, nestedWindow,
        cantorHandoff, finiteNetWitness, realSeal, transport, replay, provenance,
        nameCert]

def finiteIntersectionPropertyToEventFlow :
    FiniteIntersectionPropertyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map finiteIntersectionPropertyEncodeBHist
        (finiteIntersectionPropertyFields x)

private def finiteIntersectionPropertyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteIntersectionPropertyEventAt index rest

def finiteIntersectionPropertyFromEventFlow :
    EventFlow → Option FiniteIntersectionPropertyUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (FiniteIntersectionPropertyUp.mk
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 0 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 1 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 2 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 3 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 4 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 5 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 6 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 7 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 8 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 9 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 10 ef))
          (finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEventAt 11 ef)))

private theorem FiniteIntersectionPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteIntersectionPropertyUp,
      finiteIntersectionPropertyFromEventFlow (finiteIntersectionPropertyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk index closedFamily acceptance closedIntervalCompletion nestedWindow cantorHandoff
      finiteNetWitness realSeal transport replay provenance nameCert =>
      change
        some
          (FiniteIntersectionPropertyUp.mk
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist index))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist closedFamily))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist acceptance))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist closedIntervalCompletion))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist nestedWindow))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist cantorHandoff))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist finiteNetWitness))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist realSeal))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist transport))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist replay))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist provenance))
            (finiteIntersectionPropertyDecodeBHist
              (finiteIntersectionPropertyEncodeBHist nameCert))) =
          some
            (FiniteIntersectionPropertyUp.mk index closedFamily acceptance
              closedIntervalCompletion nestedWindow cantorHandoff finiteNetWitness
              realSeal transport replay provenance nameCert)
      rw [FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode index,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode closedFamily,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode acceptance,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode
          closedIntervalCompletion,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode nestedWindow,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode cantorHandoff,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode
          finiteNetWitness,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode realSeal,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode transport,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode replay,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode provenance,
        FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode nameCert]

private theorem FiniteIntersectionPropertyTasteGate_single_carrier_alignment_injective
    {x y : FiniteIntersectionPropertyUp} :
    finiteIntersectionPropertyToEventFlow x = finiteIntersectionPropertyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteIntersectionPropertyFromEventFlow (finiteIntersectionPropertyToEventFlow x) =
        finiteIntersectionPropertyFromEventFlow (finiteIntersectionPropertyToEventFlow y) :=
    congrArg finiteIntersectionPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteIntersectionPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteIntersectionPropertyTasteGate_single_carrier_alignment_round_trip y)))

private theorem finiteIntersectionProperty_field_faithful :
    ∀ x y : FiniteIntersectionPropertyUp,
      finiteIntersectionPropertyFields x = finiteIntersectionPropertyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk index1 closedFamily1 acceptance1 closedIntervalCompletion1 nestedWindow1
      cantorHandoff1 finiteNetWitness1 realSeal1 transport1 replay1 provenance1
      nameCert1 =>
      cases y with
      | mk index2 closedFamily2 acceptance2 closedIntervalCompletion2 nestedWindow2
          cantorHandoff2 finiteNetWitness2 realSeal2 transport2 replay2 provenance2
          nameCert2 =>
          cases h
          rfl

instance finiteIntersectionPropertyBHistCarrier :
    BHistCarrier FiniteIntersectionPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteIntersectionPropertyToEventFlow
  fromEventFlow := finiteIntersectionPropertyFromEventFlow

instance finiteIntersectionPropertyChapterTasteGate :
    ChapterTasteGate FiniteIntersectionPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteIntersectionPropertyFromEventFlow (finiteIntersectionPropertyToEventFlow x) =
        some x
    exact FiniteIntersectionPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteIntersectionPropertyTasteGate_single_carrier_alignment_injective heq)

instance finiteIntersectionPropertyFieldFaithful :
    FieldFaithful FiniteIntersectionPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteIntersectionPropertyFields
  field_faithful := finiteIntersectionProperty_field_faithful

instance finiteIntersectionPropertyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteIntersectionPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteIntersectionPropertyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FiniteIntersectionPropertyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteIntersectionPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteIntersectionPropertyChapterTasteGate

theorem FiniteIntersectionPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteIntersectionPropertyDecodeBHist (finiteIntersectionPropertyEncodeBHist h) =
        h) ∧
      (∀ x : FiniteIntersectionPropertyUp,
        finiteIntersectionPropertyFromEventFlow (finiteIntersectionPropertyToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteIntersectionPropertyUp,
          finiteIntersectionPropertyToEventFlow x =
              finiteIntersectionPropertyToEventFlow y →
            x = y) ∧
          finiteIntersectionPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FiniteIntersectionPropertyTasteGate_single_carrier_alignment_decode
  · constructor
    · exact FiniteIntersectionPropertyTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FiniteIntersectionPropertyTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.FiniteIntersectionPropertyUp
