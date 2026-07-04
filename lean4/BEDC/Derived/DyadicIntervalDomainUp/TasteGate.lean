import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalDomainUp : Type where
  | mk (L U R Delta W Q E H C P N : BHist) : DyadicIntervalDomainUp
  deriving DecidableEq

def dyadicIntervalDomainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalDomainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalDomainEncodeBHist h

def dyadicIntervalDomainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalDomainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalDomainDecodeBHist tail)

private theorem DyadicIntervalDomainTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalDomainFields : DyadicIntervalDomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalDomainUp.mk L U R Delta W Q E H C P N =>
      [L, U, R, Delta, W, Q, E, H, C, P, N]

def dyadicIntervalDomainToEventFlow : DyadicIntervalDomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalDomainFields x).map dyadicIntervalDomainEncodeBHist

private def dyadicIntervalDomainEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalDomainEventAt index rest

def dyadicIntervalDomainFromEventFlow
    (ef : EventFlow) : Option DyadicIntervalDomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalDomainUp.mk
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 0 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 1 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 2 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 3 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 4 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 5 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 6 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 7 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 8 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 9 ef))
      (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEventAt 10 ef)))

private theorem DyadicIntervalDomainTasteGate_single_carrier_alignment_round_trip
    (x : DyadicIntervalDomainUp) :
    dyadicIntervalDomainFromEventFlow (dyadicIntervalDomainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U R Delta W Q E H C P N =>
      change
        some
          (DyadicIntervalDomainUp.mk
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist L))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist U))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist R))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist Delta))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist W))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist Q))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist E))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist H))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist C))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist P))
            (dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist N))) =
          some (DyadicIntervalDomainUp.mk L U R Delta W Q E H C P N)
      rw [DyadicIntervalDomainTasteGate_single_carrier_alignment_decode L,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode U,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode R,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode Delta,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode W,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode Q,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode E,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode H,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode C,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode P,
        DyadicIntervalDomainTasteGate_single_carrier_alignment_decode N]

private theorem DyadicIntervalDomainTasteGate_single_carrier_alignment_injective
    {x y : DyadicIntervalDomainUp} :
    dyadicIntervalDomainToEventFlow x = dyadicIntervalDomainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalDomainFromEventFlow (dyadicIntervalDomainToEventFlow x) =
        dyadicIntervalDomainFromEventFlow (dyadicIntervalDomainToEventFlow y) :=
    congrArg dyadicIntervalDomainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalDomainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalDomainTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicIntervalDomainTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicIntervalDomainUp,
      dyadicIntervalDomainFields x = dyadicIntervalDomainFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ U₁ R₁ Delta₁ W₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ U₂ R₂ Delta₂ W₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicIntervalDomainBHistCarrier :
    BHistCarrier DyadicIntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalDomainToEventFlow
  fromEventFlow := dyadicIntervalDomainFromEventFlow

instance dyadicIntervalDomainChapterTasteGate :
    ChapterTasteGate DyadicIntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalDomainFromEventFlow (dyadicIntervalDomainToEventFlow x) =
      some x
    exact DyadicIntervalDomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalDomainTasteGate_single_carrier_alignment_injective heq)

instance dyadicIntervalDomainFieldFaithful :
    FieldFaithful DyadicIntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalDomainFields
  field_faithful := DyadicIntervalDomainTasteGate_single_carrier_alignment_fields

instance dyadicIntervalDomainNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicIntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicIntervalDomainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DyadicIntervalDomainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DyadicIntervalDomainTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicIntervalDomainDecodeBHist (dyadicIntervalDomainEncodeBHist h) = h) ∧
      (∀ x : DyadicIntervalDomainUp,
        dyadicIntervalDomainFromEventFlow (dyadicIntervalDomainToEventFlow x) =
          some x) ∧
        (∀ x y : DyadicIntervalDomainUp,
          dyadicIntervalDomainToEventFlow x = dyadicIntervalDomainToEventFlow y →
            x = y) ∧
          dyadicIntervalDomainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact DyadicIntervalDomainTasteGate_single_carrier_alignment_decode
  constructor
  · exact DyadicIntervalDomainTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact DyadicIntervalDomainTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.DyadicIntervalDomainUp
