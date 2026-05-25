import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformIntegralLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformIntegralLimitUp : Type where
  | mk (I F T J A Q E H C P N : BHist) : UniformIntegralLimitUp
  deriving DecidableEq

def uniformIntegralLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformIntegralLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformIntegralLimitEncodeBHist h

def uniformIntegralLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformIntegralLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformIntegralLimitDecodeBHist tail)

private theorem UniformIntegralLimitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformIntegralLimitFields : UniformIntegralLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformIntegralLimitUp.mk I F T J A Q E H C P N => [I, F, T, J, A, Q, E, H, C, P, N]

def uniformIntegralLimitToEventFlow : UniformIntegralLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformIntegralLimitFields x).map uniformIntegralLimitEncodeBHist

private def uniformIntegralLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformIntegralLimitEventAtDefault index rest

def uniformIntegralLimitFromEventFlow (ef : EventFlow) : Option UniformIntegralLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformIntegralLimitUp.mk
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 0 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 1 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 2 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 3 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 4 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 5 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 6 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 7 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 8 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 9 ef))
      (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEventAtDefault 10 ef)))

private theorem UniformIntegralLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformIntegralLimitUp,
      uniformIntegralLimitFromEventFlow (uniformIntegralLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I F T J A Q E H C P N =>
      change
        some
          (UniformIntegralLimitUp.mk
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist I))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist F))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist T))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist J))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist A))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist Q))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist E))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist H))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist C))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist P))
            (uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist N))) =
          some (UniformIntegralLimitUp.mk I F T J A Q E H C P N)
      rw [UniformIntegralLimitTasteGate_single_carrier_alignment_decode I,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode F,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode T,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode J,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode A,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode Q,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode E,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode H,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode C,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode P,
        UniformIntegralLimitTasteGate_single_carrier_alignment_decode N]

private theorem UniformIntegralLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformIntegralLimitUp} :
    uniformIntegralLimitToEventFlow x = uniformIntegralLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformIntegralLimitFromEventFlow (uniformIntegralLimitToEventFlow x) =
        uniformIntegralLimitFromEventFlow (uniformIntegralLimitToEventFlow y) :=
    congrArg uniformIntegralLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformIntegralLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformIntegralLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformIntegralLimitTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformIntegralLimitUp,
      uniformIntegralLimitFields x = uniformIntegralLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 F1 T1 J1 A1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 F2 T2 J2 A2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformIntegralLimitBHistCarrier : BHistCarrier UniformIntegralLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformIntegralLimitToEventFlow
  fromEventFlow := uniformIntegralLimitFromEventFlow

instance uniformIntegralLimitChapterTasteGate : ChapterTasteGate UniformIntegralLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformIntegralLimitFromEventFlow (uniformIntegralLimitToEventFlow x) = some x
    exact UniformIntegralLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformIntegralLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformIntegralLimitFieldFaithful : FieldFaithful UniformIntegralLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformIntegralLimitFields
  field_faithful := UniformIntegralLimitTasteGate_single_carrier_alignment_fields

instance uniformIntegralLimitNontrivial : Nontrivial UniformIntegralLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformIntegralLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformIntegralLimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformIntegralLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformIntegralLimitChapterTasteGate

theorem UniformIntegralLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformIntegralLimitDecodeBHist (uniformIntegralLimitEncodeBHist h) = h) ∧
      (∀ x : UniformIntegralLimitUp,
        uniformIntegralLimitFromEventFlow (uniformIntegralLimitToEventFlow x) = some x) ∧
        (∀ x y : UniformIntegralLimitUp,
          uniformIntegralLimitToEventFlow x = uniformIntegralLimitToEventFlow y → x = y) ∧
          uniformIntegralLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨UniformIntegralLimitTasteGate_single_carrier_alignment_decode,
      UniformIntegralLimitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformIntegralLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformIntegralLimitUp
