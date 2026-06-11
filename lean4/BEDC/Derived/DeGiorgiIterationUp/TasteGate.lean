import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DeGiorgiIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DeGiorgiIterationUp : Type where
  | mk (L T S P M B Q R H C G N : BHist) : DeGiorgiIterationUp
  deriving DecidableEq

def deGiorgiIterationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: deGiorgiIterationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: deGiorgiIterationEncodeBHist h

def deGiorgiIterationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (deGiorgiIterationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (deGiorgiIterationDecodeBHist tail)

private theorem DeGiorgiIterationTasteGate_decode :
    ∀ h : BHist, deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def deGiorgiIterationFields : DeGiorgiIterationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DeGiorgiIterationUp.mk L T S P M B Q R H C G N => [L, T, S, P, M, B, Q, R, H, C, G, N]

def deGiorgiIterationToEventFlow : DeGiorgiIterationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (deGiorgiIterationFields x).map deGiorgiIterationEncodeBHist

private def deGiorgiIterationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => deGiorgiIterationEventAtDefault index rest

def deGiorgiIterationFromEventFlow (ef : EventFlow) : Option DeGiorgiIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DeGiorgiIterationUp.mk
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 0 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 1 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 2 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 3 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 4 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 5 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 6 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 7 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 8 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 9 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 10 ef))
      (deGiorgiIterationDecodeBHist (deGiorgiIterationEventAtDefault 11 ef)))

private theorem DeGiorgiIterationTasteGate_round_trip :
    ∀ x : DeGiorgiIterationUp,
      deGiorgiIterationFromEventFlow (deGiorgiIterationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L T S P M B Q R H C G N =>
      change
        some
          (DeGiorgiIterationUp.mk
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist L))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist T))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist S))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist P))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist M))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist B))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist Q))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist R))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist H))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist C))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist G))
            (deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist N))) =
          some (DeGiorgiIterationUp.mk L T S P M B Q R H C G N)
      rw [DeGiorgiIterationTasteGate_decode L, DeGiorgiIterationTasteGate_decode T,
        DeGiorgiIterationTasteGate_decode S, DeGiorgiIterationTasteGate_decode P,
        DeGiorgiIterationTasteGate_decode M, DeGiorgiIterationTasteGate_decode B,
        DeGiorgiIterationTasteGate_decode Q, DeGiorgiIterationTasteGate_decode R,
        DeGiorgiIterationTasteGate_decode H, DeGiorgiIterationTasteGate_decode C,
        DeGiorgiIterationTasteGate_decode G, DeGiorgiIterationTasteGate_decode N]

private theorem DeGiorgiIterationTasteGate_toEventFlow_injective {x y : DeGiorgiIterationUp} :
    deGiorgiIterationToEventFlow x = deGiorgiIterationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      deGiorgiIterationFromEventFlow (deGiorgiIterationToEventFlow x) =
        deGiorgiIterationFromEventFlow (deGiorgiIterationToEventFlow y) :=
    congrArg deGiorgiIterationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DeGiorgiIterationTasteGate_round_trip x).symm
      (Eq.trans hread (DeGiorgiIterationTasteGate_round_trip y)))

private theorem DeGiorgiIterationTasteGate_fields :
    ∀ x y : DeGiorgiIterationUp, deGiorgiIterationFields x = deGiorgiIterationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 T1 S1 P1 M1 B1 Q1 R1 H1 C1 G1 N1 =>
      cases y with
      | mk L2 T2 S2 P2 M2 B2 Q2 R2 H2 C2 G2 N2 =>
          cases hfields
          rfl

instance deGiorgiIterationBHistCarrier : BHistCarrier DeGiorgiIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := deGiorgiIterationToEventFlow
  fromEventFlow := deGiorgiIterationFromEventFlow

instance deGiorgiIterationChapterTasteGate : ChapterTasteGate DeGiorgiIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change deGiorgiIterationFromEventFlow (deGiorgiIterationToEventFlow x) = some x
    exact DeGiorgiIterationTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DeGiorgiIterationTasteGate_toEventFlow_injective heq)

instance deGiorgiIterationFieldFaithful : FieldFaithful DeGiorgiIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := deGiorgiIterationFields
  field_faithful := DeGiorgiIterationTasteGate_fields

instance deGiorgiIterationNontrivial : Nontrivial DeGiorgiIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DeGiorgiIterationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DeGiorgiIterationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DeGiorgiIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  deGiorgiIterationChapterTasteGate

theorem DeGiorgiIterationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DeGiorgiIterationUp) ∧
      Nonempty (FieldFaithful DeGiorgiIterationUp) ∧
        Nonempty (Nontrivial DeGiorgiIterationUp) ∧
          (∀ h : BHist,
            deGiorgiIterationDecodeBHist (deGiorgiIterationEncodeBHist h) = h) ∧
            (∀ x : DeGiorgiIterationUp,
              deGiorgiIterationFromEventFlow (deGiorgiIterationToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨deGiorgiIterationChapterTasteGate⟩,
      ⟨deGiorgiIterationFieldFaithful⟩,
      ⟨deGiorgiIterationNontrivial⟩,
      DeGiorgiIterationTasteGate_decode,
      DeGiorgiIterationTasteGate_round_trip⟩

end BEDC.Derived.DeGiorgiIterationUp
