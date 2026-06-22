import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DavenportConstantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DavenportConstantUp : Type where
  | mk (G A L S W R H C P N : BHist) : DavenportConstantUp
  deriving DecidableEq

def davenportConstantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: davenportConstantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: davenportConstantEncodeBHist h

def davenportConstantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (davenportConstantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (davenportConstantDecodeBHist tail)

private theorem DavenportConstantTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, davenportConstantDecodeBHist (davenportConstantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def davenportConstantFields : DavenportConstantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DavenportConstantUp.mk G A L S W R H C P N => [G, A, L, S, W, R, H, C, P, N]

def davenportConstantToEventFlow : DavenportConstantUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (davenportConstantFields x).map davenportConstantEncodeBHist

private def davenportConstantEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => davenportConstantEventAtDefault index rest

def davenportConstantFromEventFlow (ef : EventFlow) : Option DavenportConstantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DavenportConstantUp.mk
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 0 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 1 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 2 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 3 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 4 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 5 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 6 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 7 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 8 ef))
      (davenportConstantDecodeBHist (davenportConstantEventAtDefault 9 ef)))

private theorem DavenportConstantTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DavenportConstantUp,
      davenportConstantFromEventFlow (davenportConstantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G A L S W R H C P N =>
      change
        some
          (DavenportConstantUp.mk
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist G))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist A))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist L))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist S))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist W))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist R))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist H))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist C))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist P))
            (davenportConstantDecodeBHist (davenportConstantEncodeBHist N))) =
          some (DavenportConstantUp.mk G A L S W R H C P N)
      rw [DavenportConstantTasteGate_single_carrier_alignment_decode G,
        DavenportConstantTasteGate_single_carrier_alignment_decode A,
        DavenportConstantTasteGate_single_carrier_alignment_decode L,
        DavenportConstantTasteGate_single_carrier_alignment_decode S,
        DavenportConstantTasteGate_single_carrier_alignment_decode W,
        DavenportConstantTasteGate_single_carrier_alignment_decode R,
        DavenportConstantTasteGate_single_carrier_alignment_decode H,
        DavenportConstantTasteGate_single_carrier_alignment_decode C,
        DavenportConstantTasteGate_single_carrier_alignment_decode P,
        DavenportConstantTasteGate_single_carrier_alignment_decode N]

private theorem DavenportConstantToEventFlow_injective {x y : DavenportConstantUp} :
    davenportConstantToEventFlow x = davenportConstantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      davenportConstantFromEventFlow (davenportConstantToEventFlow x) =
        davenportConstantFromEventFlow (davenportConstantToEventFlow y) :=
    congrArg davenportConstantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DavenportConstantTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DavenportConstantTasteGate_single_carrier_alignment_round_trip y)))

private theorem DavenportConstantTasteGate_single_carrier_alignment_fields :
    ∀ x y : DavenportConstantUp, davenportConstantFields x = davenportConstantFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ A₁ L₁ S₁ W₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ A₂ L₂ S₂ W₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance davenportConstantBHistCarrier : BHistCarrier DavenportConstantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := davenportConstantToEventFlow
  fromEventFlow := davenportConstantFromEventFlow

instance davenportConstantChapterTasteGate : ChapterTasteGate DavenportConstantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change davenportConstantFromEventFlow (davenportConstantToEventFlow x) = some x
    exact DavenportConstantTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DavenportConstantToEventFlow_injective heq)

instance davenportConstantFieldFaithful : FieldFaithful DavenportConstantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := davenportConstantFields
  field_faithful := DavenportConstantTasteGate_single_carrier_alignment_fields

instance davenportConstantNontrivial : Nontrivial DavenportConstantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DavenportConstantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DavenportConstantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DavenportConstantTasteGate_single_carrier_alignment :
    (∀ h : BHist, davenportConstantDecodeBHist (davenportConstantEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DavenportConstantUp) ∧
        Nonempty (ChapterTasteGate DavenportConstantUp) ∧
          davenportConstantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DavenportConstantTasteGate_single_carrier_alignment_decode,
      ⟨davenportConstantBHistCarrier⟩, ⟨davenportConstantChapterTasteGate⟩, rfl⟩

end BEDC.Derived.DavenportConstantUp
