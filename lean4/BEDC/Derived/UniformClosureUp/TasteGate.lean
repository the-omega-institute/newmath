import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformClosureUp : Type where
  | mk (M Q S L E W R Z H C P N : BHist) : UniformClosureUp
  deriving DecidableEq

def uniformClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformClosureEncodeBHist h

def uniformClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformClosureDecodeBHist tail)

private theorem UniformClosureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformClosureDecodeBHist (uniformClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformClosureFields : UniformClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformClosureUp.mk M Q S L E W R Z H C P N => [M, Q, S, L, E, W, R, Z, H, C, P, N]

def uniformClosureToEventFlow : UniformClosureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformClosureFields x).map uniformClosureEncodeBHist

private def uniformClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformClosureEventAtDefault index rest

def uniformClosureFromEventFlow (ef : EventFlow) : Option UniformClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformClosureUp.mk
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 0 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 1 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 2 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 3 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 4 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 5 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 6 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 7 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 8 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 9 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 10 ef))
      (uniformClosureDecodeBHist (uniformClosureEventAtDefault 11 ef)))

private theorem UniformClosureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformClosureUp,
      uniformClosureFromEventFlow (uniformClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M Q S L E W R Z H C P N =>
      change
        some
          (UniformClosureUp.mk
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist M))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist Q))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist S))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist L))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist E))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist W))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist R))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist Z))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist H))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist C))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist P))
            (uniformClosureDecodeBHist (uniformClosureEncodeBHist N))) =
          some (UniformClosureUp.mk M Q S L E W R Z H C P N)
      rw [UniformClosureTasteGate_single_carrier_alignment_decode M,
        UniformClosureTasteGate_single_carrier_alignment_decode Q,
        UniformClosureTasteGate_single_carrier_alignment_decode S,
        UniformClosureTasteGate_single_carrier_alignment_decode L,
        UniformClosureTasteGate_single_carrier_alignment_decode E,
        UniformClosureTasteGate_single_carrier_alignment_decode W,
        UniformClosureTasteGate_single_carrier_alignment_decode R,
        UniformClosureTasteGate_single_carrier_alignment_decode Z,
        UniformClosureTasteGate_single_carrier_alignment_decode H,
        UniformClosureTasteGate_single_carrier_alignment_decode C,
        UniformClosureTasteGate_single_carrier_alignment_decode P,
        UniformClosureTasteGate_single_carrier_alignment_decode N]

private theorem UniformClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformClosureUp} :
    uniformClosureToEventFlow x = uniformClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformClosureFromEventFlow (uniformClosureToEventFlow x) =
        uniformClosureFromEventFlow (uniformClosureToEventFlow y) :=
    congrArg uniformClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformClosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformClosureTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformClosureUp, uniformClosureFields x = uniformClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 Q1 S1 L1 E1 W1 R1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 Q2 S2 L2 E2 W2 R2 Z2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformClosureBHistCarrier : BHistCarrier UniformClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformClosureToEventFlow
  fromEventFlow := uniformClosureFromEventFlow

instance uniformClosureChapterTasteGate : ChapterTasteGate UniformClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformClosureFromEventFlow (uniformClosureToEventFlow x) = some x
    exact UniformClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformClosureFieldFaithful : FieldFaithful UniformClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformClosureFields
  field_faithful := UniformClosureTasteGate_single_carrier_alignment_fields

instance uniformClosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformClosureChapterTasteGate

theorem UniformClosureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformClosureUp) ∧
      Nonempty (FieldFaithful UniformClosureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial UniformClosureUp) ∧
          (∀ h : BHist, uniformClosureDecodeBHist (uniformClosureEncodeBHist h) = h) ∧
            (∀ x : UniformClosureUp,
              uniformClosureFromEventFlow (uniformClosureToEventFlow x) = some x) ∧
              (∀ x y : UniformClosureUp,
                uniformClosureToEventFlow x = uniformClosureToEventFlow y -> x = y) ∧
                uniformClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨uniformClosureChapterTasteGate⟩,
      ⟨uniformClosureFieldFaithful⟩,
      ⟨uniformClosureNontrivial⟩,
      UniformClosureTasteGate_single_carrier_alignment_decode,
      UniformClosureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => UniformClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformClosureUp
