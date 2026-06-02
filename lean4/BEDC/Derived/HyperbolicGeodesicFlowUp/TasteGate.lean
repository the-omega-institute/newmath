import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicGeodesicFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicGeodesicFlowUp : Type where
  | mk (U M B T D F J A H C P N : BHist) : HyperbolicGeodesicFlowUp
  deriving DecidableEq

def hyperbolicGeodesicFlowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicGeodesicFlowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicGeodesicFlowEncodeBHist h

def hyperbolicGeodesicFlowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicGeodesicFlowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicGeodesicFlowDecodeBHist tail)

private theorem HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicGeodesicFlowFields : HyperbolicGeodesicFlowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicGeodesicFlowUp.mk U M B T D F J A H C P N =>
      [U, M, B, T, D, F, J, A, H, C, P, N]

def hyperbolicGeodesicFlowToEventFlow : HyperbolicGeodesicFlowUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hyperbolicGeodesicFlowFields x).map hyperbolicGeodesicFlowEncodeBHist

private def hyperbolicGeodesicFlowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicGeodesicFlowEventAtDefault index rest

def hyperbolicGeodesicFlowFromEventFlow
    (ef : EventFlow) : Option HyperbolicGeodesicFlowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicGeodesicFlowUp.mk
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 0 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 1 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 2 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 3 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 4 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 5 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 6 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 7 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 8 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 9 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 10 ef))
      (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEventAtDefault 11 ef)))

private theorem HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HyperbolicGeodesicFlowUp,
      hyperbolicGeodesicFlowFromEventFlow
        (hyperbolicGeodesicFlowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U M B T D F J A H C P N =>
      change
        some
          (HyperbolicGeodesicFlowUp.mk
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist U))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist M))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist B))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist T))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist D))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist F))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist J))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist A))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist H))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist C))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist P))
            (hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist N))) =
          some (HyperbolicGeodesicFlowUp.mk U M B T D F J A H C P N)
      rw [HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode U,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode M,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode B,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode T,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode D,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode F,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode J,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode A,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode H,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode C,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode P,
        HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode N]

private theorem HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicGeodesicFlowUp} :
    hyperbolicGeodesicFlowToEventFlow x = hyperbolicGeodesicFlowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicGeodesicFlowFromEventFlow (hyperbolicGeodesicFlowToEventFlow x) =
        hyperbolicGeodesicFlowFromEventFlow (hyperbolicGeodesicFlowToEventFlow y) :=
    congrArg hyperbolicGeodesicFlowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_fields :
    ∀ x y : HyperbolicGeodesicFlowUp,
      hyperbolicGeodesicFlowFields x = hyperbolicGeodesicFlowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 M1 B1 T1 D1 F1 J1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 M2 B2 T2 D2 F2 J2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicGeodesicFlowBHistCarrier : BHistCarrier HyperbolicGeodesicFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicGeodesicFlowToEventFlow
  fromEventFlow := hyperbolicGeodesicFlowFromEventFlow

instance hyperbolicGeodesicFlowChapterTasteGate :
    ChapterTasteGate HyperbolicGeodesicFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicGeodesicFlowFromEventFlow (hyperbolicGeodesicFlowToEventFlow x) =
        some x
    exact HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_toEventFlow_injective
      heq)

instance hyperbolicGeodesicFlowFieldFaithful : FieldFaithful HyperbolicGeodesicFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicGeodesicFlowFields
  field_faithful := HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_fields

instance hyperbolicGeodesicFlowNontrivial : Nontrivial HyperbolicGeodesicFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicGeodesicFlowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HyperbolicGeodesicFlowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperbolicGeodesicFlowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        hyperbolicGeodesicFlowDecodeBHist (hyperbolicGeodesicFlowEncodeBHist h) = h) ∧
      (∀ x : HyperbolicGeodesicFlowUp,
        hyperbolicGeodesicFlowFromEventFlow
          (hyperbolicGeodesicFlowToEventFlow x) = some x) ∧
        hyperbolicGeodesicFlowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_decode,
      HyperbolicGeodesicFlowTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.HyperbolicGeodesicFlowUp
