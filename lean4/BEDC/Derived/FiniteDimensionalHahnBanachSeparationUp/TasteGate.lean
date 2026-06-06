import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDimensionalHahnBanachSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDimensionalHahnBanachSeparationUp : Type where
  | mk (V B L N R Q C E H T P M : BHist) : FiniteDimensionalHahnBanachSeparationUp
  deriving DecidableEq

def finiteDimensionalHahnBanachSeparationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDimensionalHahnBanachSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDimensionalHahnBanachSeparationEncodeBHist h

def finiteDimensionalHahnBanachSeparationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDimensionalHahnBanachSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDimensionalHahnBanachSeparationDecodeBHist tail)

private theorem FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDimensionalHahnBanachSeparationFields :
    FiniteDimensionalHahnBanachSeparationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalHahnBanachSeparationUp.mk V B L N R Q C E H T P M =>
      [V, B, L, N, R, Q, C, E, H, T, P, M]

def finiteDimensionalHahnBanachSeparationToEventFlow :
    FiniteDimensionalHahnBanachSeparationUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (finiteDimensionalHahnBanachSeparationFields x).map
      finiteDimensionalHahnBanachSeparationEncodeBHist

private def finiteDimensionalHahnBanachSeparationEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteDimensionalHahnBanachSeparationEventAtDefault index rest

def finiteDimensionalHahnBanachSeparationFromEventFlow
    (ef : EventFlow) : Option FiniteDimensionalHahnBanachSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDimensionalHahnBanachSeparationUp.mk
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 0 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 1 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 2 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 3 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 4 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 5 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 6 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 7 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 8 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 9 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 10 ef))
      (finiteDimensionalHahnBanachSeparationDecodeBHist
        (finiteDimensionalHahnBanachSeparationEventAtDefault 11 ef)))

private theorem FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteDimensionalHahnBanachSeparationUp,
      finiteDimensionalHahnBanachSeparationFromEventFlow
        (finiteDimensionalHahnBanachSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V B L N R Q C E H T P M =>
      change
        some
          (FiniteDimensionalHahnBanachSeparationUp.mk
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist V))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist B))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist L))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist N))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist R))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist Q))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist C))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist E))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist H))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist T))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist P))
            (finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist M))) =
          some (FiniteDimensionalHahnBanachSeparationUp.mk V B L N R Q C E H T P M)
      rw [FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode V,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode B,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode L,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode N,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode R,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode Q,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode C,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode E,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode H,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode T,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode P,
        FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode M]

private theorem FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteDimensionalHahnBanachSeparationUp} :
    finiteDimensionalHahnBanachSeparationToEventFlow x =
      finiteDimensionalHahnBanachSeparationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDimensionalHahnBanachSeparationFromEventFlow
          (finiteDimensionalHahnBanachSeparationToEventFlow x) =
        finiteDimensionalHahnBanachSeparationFromEventFlow
          (finiteDimensionalHahnBanachSeparationToEventFlow y) :=
    congrArg finiteDimensionalHahnBanachSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_fields :
    forall x y : FiniteDimensionalHahnBanachSeparationUp,
      finiteDimensionalHahnBanachSeparationFields x =
        finiteDimensionalHahnBanachSeparationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 B1 L1 N1 R1 Q1 C1 E1 H1 T1 P1 M1 =>
      cases y with
      | mk V2 B2 L2 N2 R2 Q2 C2 E2 H2 T2 P2 M2 =>
          cases hfields
          rfl

instance finiteDimensionalHahnBanachSeparationBHistCarrier :
    BHistCarrier FiniteDimensionalHahnBanachSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDimensionalHahnBanachSeparationToEventFlow
  fromEventFlow := finiteDimensionalHahnBanachSeparationFromEventFlow

instance finiteDimensionalHahnBanachSeparationChapterTasteGate :
    ChapterTasteGate FiniteDimensionalHahnBanachSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDimensionalHahnBanachSeparationFromEventFlow
        (finiteDimensionalHahnBanachSeparationToEventFlow x) = some x
    exact
      FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance finiteDimensionalHahnBanachSeparationFieldFaithful :
    FieldFaithful FiniteDimensionalHahnBanachSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDimensionalHahnBanachSeparationFields
  field_faithful :=
    FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_fields

instance finiteDimensionalHahnBanachSeparationNontrivial :
    Nontrivial FiniteDimensionalHahnBanachSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDimensionalHahnBanachSeparationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FiniteDimensionalHahnBanachSeparationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteDimensionalHahnBanachSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteDimensionalHahnBanachSeparationChapterTasteGate

theorem FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteDimensionalHahnBanachSeparationUp) ∧
      Nonempty (FieldFaithful FiniteDimensionalHahnBanachSeparationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteDimensionalHahnBanachSeparationUp) ∧
          (forall h : BHist,
            finiteDimensionalHahnBanachSeparationDecodeBHist
              (finiteDimensionalHahnBanachSeparationEncodeBHist h) = h) ∧
            (forall x : FiniteDimensionalHahnBanachSeparationUp,
              finiteDimensionalHahnBanachSeparationFromEventFlow
                (finiteDimensionalHahnBanachSeparationToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨finiteDimensionalHahnBanachSeparationChapterTasteGate⟩,
      ⟨finiteDimensionalHahnBanachSeparationFieldFaithful⟩,
      ⟨finiteDimensionalHahnBanachSeparationNontrivial⟩,
      FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_decode,
      FiniteDimensionalHahnBanachSeparationTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.FiniteDimensionalHahnBanachSeparationUp
