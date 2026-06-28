import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WijsmanTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

namespace TasteGate

inductive WijsmanTopologyUp : Type where
  | mk (M H D S R E V F T C P N : BHist) : WijsmanTopologyUp
  deriving DecidableEq

def wijsmanTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wijsmanTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wijsmanTopologyEncodeBHist h

def wijsmanTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wijsmanTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wijsmanTopologyDecodeBHist tail)

private theorem WijsmanTopologyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def wijsmanTopologyFields : WijsmanTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WijsmanTopologyUp.mk M H D S R E V F T C P N => [M, H, D, S, R, E, V, F, T, C, P, N]

def wijsmanTopologyToEventFlow : WijsmanTopologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (wijsmanTopologyFields x).map wijsmanTopologyEncodeBHist

private def wijsmanTopologyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => wijsmanTopologyEventAtDefault index rest

def wijsmanTopologyFromEventFlow (ef : EventFlow) : Option WijsmanTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WijsmanTopologyUp.mk
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 0 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 1 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 2 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 3 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 4 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 5 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 6 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 7 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 8 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 9 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 10 ef))
      (wijsmanTopologyDecodeBHist (wijsmanTopologyEventAtDefault 11 ef)))

private theorem WijsmanTopologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WijsmanTopologyUp,
      wijsmanTopologyFromEventFlow (wijsmanTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M H D S R E V F T C P N =>
      change
        some
          (WijsmanTopologyUp.mk
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist M))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist H))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist D))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist S))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist R))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist E))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist V))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist F))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist T))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist C))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist P))
            (wijsmanTopologyDecodeBHist (wijsmanTopologyEncodeBHist N))) =
          some (WijsmanTopologyUp.mk M H D S R E V F T C P N)
      rw [WijsmanTopologyTasteGate_single_carrier_alignment_decode M,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode H,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode D,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode S,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode R,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode E,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode V,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode F,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode T,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode C,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode P,
        WijsmanTopologyTasteGate_single_carrier_alignment_decode N]

private theorem WijsmanTopologyTasteGate_single_carrier_alignment_injective
    {x y : WijsmanTopologyUp} :
    wijsmanTopologyToEventFlow x = wijsmanTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      wijsmanTopologyFromEventFlow (wijsmanTopologyToEventFlow x) =
        wijsmanTopologyFromEventFlow (wijsmanTopologyToEventFlow y) :=
    congrArg wijsmanTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WijsmanTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WijsmanTopologyTasteGate_single_carrier_alignment_round_trip y)))

private theorem WijsmanTopologyTasteGate_single_carrier_alignment_fields :
    ∀ x y : WijsmanTopologyUp, wijsmanTopologyFields x = wijsmanTopologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 H1 D1 S1 R1 E1 V1 F1 T1 C1 P1 N1 =>
      cases y with
      | mk M2 H2 D2 S2 R2 E2 V2 F2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance wijsmanTopologyBHistCarrier : BHistCarrier WijsmanTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wijsmanTopologyToEventFlow
  fromEventFlow := wijsmanTopologyFromEventFlow

instance wijsmanTopologyChapterTasteGate : ChapterTasteGate WijsmanTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change wijsmanTopologyFromEventFlow (wijsmanTopologyToEventFlow x) = some x
    exact WijsmanTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WijsmanTopologyTasteGate_single_carrier_alignment_injective heq)

instance wijsmanTopologyFieldFaithful : FieldFaithful WijsmanTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := wijsmanTopologyFields
  field_faithful := WijsmanTopologyTasteGate_single_carrier_alignment_fields

instance wijsmanTopologyNontrivial : Nontrivial WijsmanTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WijsmanTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WijsmanTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

end TasteGate

theorem WijsmanTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.wijsmanTopologyDecodeBHist (TasteGate.wijsmanTopologyEncodeBHist h) = h) ∧
      (∀ x : TasteGate.WijsmanTopologyUp,
        TasteGate.wijsmanTopologyFromEventFlow (TasteGate.wijsmanTopologyToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.WijsmanTopologyUp,
          TasteGate.wijsmanTopologyToEventFlow x = TasteGate.wijsmanTopologyToEventFlow y →
            x = y) ∧
          TasteGate.wijsmanTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨TasteGate.WijsmanTopologyTasteGate_single_carrier_alignment_decode,
      TasteGate.WijsmanTopologyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => TasteGate.WijsmanTopologyTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.WijsmanTopologyUp
