import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WhitneyExtensionFiniteJetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WhitneyExtensionFiniteJetUp : Type where
  | mk (X F J A E R H C P N : BHist) : WhitneyExtensionFiniteJetUp
  deriving DecidableEq

def whitneyExtensionFiniteJetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: whitneyExtensionFiniteJetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: whitneyExtensionFiniteJetEncodeBHist h

def whitneyExtensionFiniteJetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (whitneyExtensionFiniteJetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (whitneyExtensionFiniteJetDecodeBHist tail)

private theorem WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def whitneyExtensionFiniteJetFields : WhitneyExtensionFiniteJetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WhitneyExtensionFiniteJetUp.mk X F J A E R H C P N => [X, F, J, A, E, R, H, C, P, N]

def whitneyExtensionFiniteJetToEventFlow : WhitneyExtensionFiniteJetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (whitneyExtensionFiniteJetFields x).map whitneyExtensionFiniteJetEncodeBHist

private def whitneyExtensionFiniteJetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => whitneyExtensionFiniteJetEventAtDefault index rest

def whitneyExtensionFiniteJetFromEventFlow (ef : EventFlow) :
    Option WhitneyExtensionFiniteJetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WhitneyExtensionFiniteJetUp.mk
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 0 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 1 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 2 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 3 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 4 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 5 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 6 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 7 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 8 ef))
      (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEventAtDefault 9 ef)))

private theorem WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WhitneyExtensionFiniteJetUp,
      whitneyExtensionFiniteJetFromEventFlow
          (whitneyExtensionFiniteJetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X F J A E R H C P N =>
      change
        some
          (WhitneyExtensionFiniteJetUp.mk
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist X))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist F))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist J))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist A))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist E))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist R))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist H))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist C))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist P))
            (whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist N))) =
          some (WhitneyExtensionFiniteJetUp.mk X F J A E R H C P N)
      rw [WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode X,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode F,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode J,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode A,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode E,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode R,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode H,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode C,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode P,
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode N]

private theorem WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WhitneyExtensionFiniteJetUp} :
    whitneyExtensionFiniteJetToEventFlow x = whitneyExtensionFiniteJetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      whitneyExtensionFiniteJetFromEventFlow (whitneyExtensionFiniteJetToEventFlow x) =
        whitneyExtensionFiniteJetFromEventFlow (whitneyExtensionFiniteJetToEventFlow y) :=
    congrArg whitneyExtensionFiniteJetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_round_trip y)))

private theorem WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_fields :
    ∀ x y : WhitneyExtensionFiniteJetUp, whitneyExtensionFiniteJetFields x =
      whitneyExtensionFiniteJetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 J1 A1 E1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 J2 A2 E2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance whitneyExtensionFiniteJetBHistCarrier : BHistCarrier WhitneyExtensionFiniteJetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := whitneyExtensionFiniteJetToEventFlow
  fromEventFlow := whitneyExtensionFiniteJetFromEventFlow

instance whitneyExtensionFiniteJetChapterTasteGate :
    ChapterTasteGate WhitneyExtensionFiniteJetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change whitneyExtensionFiniteJetFromEventFlow
        (whitneyExtensionFiniteJetToEventFlow x) = some x
    exact WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance whitneyExtensionFiniteJetFieldFaithful : FieldFaithful WhitneyExtensionFiniteJetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := whitneyExtensionFiniteJetFields
  field_faithful := WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_fields

instance whitneyExtensionFiniteJetNontrivial : Nontrivial WhitneyExtensionFiniteJetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WhitneyExtensionFiniteJetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WhitneyExtensionFiniteJetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def whitneyExtensionFiniteJetTasteGate : ChapterTasteGate WhitneyExtensionFiniteJetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  whitneyExtensionFiniteJetChapterTasteGate

theorem WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      whitneyExtensionFiniteJetDecodeBHist (whitneyExtensionFiniteJetEncodeBHist h) = h) ∧
      (∀ x : WhitneyExtensionFiniteJetUp,
        whitneyExtensionFiniteJetFromEventFlow
          (whitneyExtensionFiniteJetToEventFlow x) = some x) ∧
        (∀ x y : WhitneyExtensionFiniteJetUp,
          whitneyExtensionFiniteJetToEventFlow x =
            whitneyExtensionFiniteJetToEventFlow y → x = y) ∧
          whitneyExtensionFiniteJetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_decode,
      WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        WhitneyExtensionFiniteJetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.WhitneyExtensionFiniteJetUp.TasteGate
