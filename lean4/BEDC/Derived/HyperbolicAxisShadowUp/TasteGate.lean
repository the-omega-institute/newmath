import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicAxisShadowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicAxisShadowUp : Type where
  | mk (T F M B R A S H C P N : BHist) : HyperbolicAxisShadowUp
  deriving DecidableEq

def hyperbolicAxisShadowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicAxisShadowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicAxisShadowEncodeBHist h

def hyperbolicAxisShadowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicAxisShadowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicAxisShadowDecodeBHist tail)

private theorem HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicAxisShadowFields : HyperbolicAxisShadowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicAxisShadowUp.mk T F M B R A S H C P N =>
      [T, F, M, B, R, A, S, H, C, P, N]

def hyperbolicAxisShadowToEventFlow : HyperbolicAxisShadowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicAxisShadowFields x).map hyperbolicAxisShadowEncodeBHist

private def hyperbolicAxisShadowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicAxisShadowEventAtDefault index rest

def hyperbolicAxisShadowFromEventFlow
    (ef : EventFlow) : Option HyperbolicAxisShadowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicAxisShadowUp.mk
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 0 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 1 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 2 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 3 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 4 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 5 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 6 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 7 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 8 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 9 ef))
      (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEventAtDefault 10 ef)))

private theorem HyperbolicAxisShadowTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicAxisShadowUp) :
    hyperbolicAxisShadowFromEventFlow
        (hyperbolicAxisShadowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T F M B R A S H C P N =>
      change
        some
          (HyperbolicAxisShadowUp.mk
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist T))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist F))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist M))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist B))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist R))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist A))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist S))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist H))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist C))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist P))
            (hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist N))) =
          some (HyperbolicAxisShadowUp.mk T F M B R A S H C P N)
      rw [HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode T,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode F,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode M,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode B,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode R,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode A,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode S,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode H,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode C,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode P,
        HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode N]

private theorem HyperbolicAxisShadowTasteGate_single_carrier_alignment_injective
    {x y : HyperbolicAxisShadowUp} :
    hyperbolicAxisShadowToEventFlow x = hyperbolicAxisShadowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicAxisShadowFromEventFlow (hyperbolicAxisShadowToEventFlow x) =
        hyperbolicAxisShadowFromEventFlow (hyperbolicAxisShadowToEventFlow y) :=
    congrArg hyperbolicAxisShadowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyperbolicAxisShadowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicAxisShadowTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicAxisShadowTasteGate_single_carrier_alignment_fields :
    ∀ x y : HyperbolicAxisShadowUp,
      hyperbolicAxisShadowFields x = hyperbolicAxisShadowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 F1 M1 B1 R1 A1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 F2 M2 B2 R2 A2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicAxisShadowBHistCarrier : BHistCarrier HyperbolicAxisShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicAxisShadowToEventFlow
  fromEventFlow := hyperbolicAxisShadowFromEventFlow

instance hyperbolicAxisShadowChapterTasteGate : ChapterTasteGate HyperbolicAxisShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicAxisShadowFromEventFlow (hyperbolicAxisShadowToEventFlow x) = some x
    exact HyperbolicAxisShadowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicAxisShadowTasteGate_single_carrier_alignment_injective heq)

instance hyperbolicAxisShadowFieldFaithful : FieldFaithful HyperbolicAxisShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicAxisShadowFields
  field_faithful := HyperbolicAxisShadowTasteGate_single_carrier_alignment_fields

instance hyperbolicAxisShadowNontrivial : Nontrivial HyperbolicAxisShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicAxisShadowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicAxisShadowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperbolicAxisShadowTasteGate_single_carrier_alignment :
    (∀ h : BHist, hyperbolicAxisShadowDecodeBHist (hyperbolicAxisShadowEncodeBHist h) = h) ∧
      (∀ x : HyperbolicAxisShadowUp,
        hyperbolicAxisShadowFromEventFlow (hyperbolicAxisShadowToEventFlow x) = some x) ∧
        (∀ x y : HyperbolicAxisShadowUp,
          hyperbolicAxisShadowToEventFlow x = hyperbolicAxisShadowToEventFlow y → x = y) ∧
          hyperbolicAxisShadowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HyperbolicAxisShadowTasteGate_single_carrier_alignment_decode,
      HyperbolicAxisShadowTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HyperbolicAxisShadowTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.HyperbolicAxisShadowUp
