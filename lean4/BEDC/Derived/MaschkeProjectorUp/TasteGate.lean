import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MaschkeProjectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MaschkeProjectorUp : Type where
  | mk (G V R S A I Q H C K N : BHist) : MaschkeProjectorUp
  deriving DecidableEq

def maschkeProjectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: maschkeProjectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: maschkeProjectorEncodeBHist h

def maschkeProjectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (maschkeProjectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (maschkeProjectorDecodeBHist tail)

private theorem MaschkeProjectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def maschkeProjectorFields : MaschkeProjectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MaschkeProjectorUp.mk G V R S A I Q H C K N => [G, V, R, S, A, I, Q, H, C, K, N]

def maschkeProjectorToEventFlow : MaschkeProjectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (maschkeProjectorFields x).map maschkeProjectorEncodeBHist

private def maschkeProjectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => maschkeProjectorEventAtDefault index rest

def maschkeProjectorFromEventFlow (ef : EventFlow) : Option MaschkeProjectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MaschkeProjectorUp.mk
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 0 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 1 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 2 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 3 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 4 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 5 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 6 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 7 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 8 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 9 ef))
      (maschkeProjectorDecodeBHist (maschkeProjectorEventAtDefault 10 ef)))

private theorem MaschkeProjectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MaschkeProjectorUp,
      maschkeProjectorFromEventFlow (maschkeProjectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G V R S A I Q H C K N =>
      change
        some
          (MaschkeProjectorUp.mk
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist G))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist V))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist R))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist S))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist A))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist I))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist Q))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist H))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist C))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist K))
            (maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist N))) =
          some (MaschkeProjectorUp.mk G V R S A I Q H C K N)
      rw [MaschkeProjectorTasteGate_single_carrier_alignment_decode G,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode V,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode R,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode S,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode A,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode I,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode Q,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode H,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode C,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode K,
        MaschkeProjectorTasteGate_single_carrier_alignment_decode N]

private theorem MaschkeProjectorToEventFlow_injective {x y : MaschkeProjectorUp} :
    maschkeProjectorToEventFlow x = maschkeProjectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      maschkeProjectorFromEventFlow (maschkeProjectorToEventFlow x) =
        maschkeProjectorFromEventFlow (maschkeProjectorToEventFlow y) :=
    congrArg maschkeProjectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MaschkeProjectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MaschkeProjectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem MaschkeProjectorTasteGate_single_carrier_alignment_fields :
    ∀ x y : MaschkeProjectorUp, maschkeProjectorFields x = maschkeProjectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ V₁ R₁ S₁ A₁ I₁ Q₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk G₂ V₂ R₂ S₂ A₂ I₂ Q₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance maschkeProjectorBHistCarrier : BHistCarrier MaschkeProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := maschkeProjectorToEventFlow
  fromEventFlow := maschkeProjectorFromEventFlow

instance maschkeProjectorChapterTasteGate : ChapterTasteGate MaschkeProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change maschkeProjectorFromEventFlow (maschkeProjectorToEventFlow x) = some x
    exact MaschkeProjectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MaschkeProjectorToEventFlow_injective heq)

instance maschkeProjectorFieldFaithful : FieldFaithful MaschkeProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := maschkeProjectorFields
  field_faithful := MaschkeProjectorTasteGate_single_carrier_alignment_fields

instance maschkeProjectorNontrivial : Nontrivial MaschkeProjectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MaschkeProjectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MaschkeProjectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MaschkeProjectorTasteGate_single_carrier_alignment :
    (∀ h : BHist, maschkeProjectorDecodeBHist (maschkeProjectorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MaschkeProjectorUp) ∧
        Nonempty (ChapterTasteGate MaschkeProjectorUp) ∧
          maschkeProjectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MaschkeProjectorTasteGate_single_carrier_alignment_decode,
      ⟨maschkeProjectorBHistCarrier⟩, ⟨maschkeProjectorChapterTasteGate⟩, rfl⟩

end BEDC.Derived.MaschkeProjectorUp
