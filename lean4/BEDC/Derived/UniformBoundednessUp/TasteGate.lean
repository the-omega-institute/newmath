import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformBoundednessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformBoundednessUp : Type where
  | mk :
      (family pointwise baire norm regseq stream transport history replay provenance nameRow :
        BHist) →
        UniformBoundednessUp
  deriving DecidableEq

def uniformBoundednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformBoundednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformBoundednessEncodeBHist h

def uniformBoundednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformBoundednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformBoundednessDecodeBHist tail)

private theorem UniformBoundednessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformBoundednessFields : UniformBoundednessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformBoundednessUp.mk family pointwise baire norm regseq stream transport history replay
      provenance nameRow =>
      [family, pointwise, baire, norm, regseq, stream, transport, history, replay, provenance,
        nameRow]

def uniformBoundednessToEventFlow : UniformBoundednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformBoundednessUp.mk family pointwise baire norm regseq stream transport history replay
      provenance nameRow =>
      (uniformBoundednessFields
          (UniformBoundednessUp.mk family pointwise baire norm regseq stream transport history
            replay provenance nameRow)).map uniformBoundednessEncodeBHist

def uniformBoundednessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformBoundednessEventAtDefault index rest

def uniformBoundednessFromEventFlow (ef : EventFlow) : Option UniformBoundednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformBoundednessUp.mk
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 0 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 1 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 2 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 3 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 4 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 5 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 6 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 7 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 8 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 9 ef))
      (uniformBoundednessDecodeBHist (uniformBoundednessEventAtDefault 10 ef)))

private theorem UniformBoundednessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformBoundednessUp,
      uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family pointwise baire norm regseq stream transport history replay provenance nameRow =>
      change
        some
          (UniformBoundednessUp.mk
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist family))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist pointwise))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist baire))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist norm))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist regseq))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist stream))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist transport))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist history))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist replay))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist provenance))
            (uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist nameRow))) =
          some
            (UniformBoundednessUp.mk family pointwise baire norm regseq stream transport history
              replay provenance nameRow)
      rw [UniformBoundednessTasteGate_single_carrier_alignment_decode family,
        UniformBoundednessTasteGate_single_carrier_alignment_decode pointwise,
        UniformBoundednessTasteGate_single_carrier_alignment_decode baire,
        UniformBoundednessTasteGate_single_carrier_alignment_decode norm,
        UniformBoundednessTasteGate_single_carrier_alignment_decode regseq,
        UniformBoundednessTasteGate_single_carrier_alignment_decode stream,
        UniformBoundednessTasteGate_single_carrier_alignment_decode transport,
        UniformBoundednessTasteGate_single_carrier_alignment_decode history,
        UniformBoundednessTasteGate_single_carrier_alignment_decode replay,
        UniformBoundednessTasteGate_single_carrier_alignment_decode provenance,
        UniformBoundednessTasteGate_single_carrier_alignment_decode nameRow]

private theorem uniformBoundednessToEventFlow_injective {x y : UniformBoundednessUp} :
    uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) =
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow y) :=
    congrArg uniformBoundednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformBoundednessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformBoundednessTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformBoundednessTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformBoundednessUp, uniformBoundednessFields x = uniformBoundednessFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk family₁ pointwise₁ baire₁ norm₁ regseq₁ stream₁ transport₁ history₁ replay₁
      provenance₁ nameRow₁ =>
      cases y with
      | mk family₂ pointwise₂ baire₂ norm₂ regseq₂ stream₂ transport₂ history₂ replay₂
          provenance₂ nameRow₂ =>
          injection hfields with hFamily tail0
          injection tail0 with hPointwise tail1
          injection tail1 with hBaire tail2
          injection tail2 with hNorm tail3
          injection tail3 with hRegseq tail4
          injection tail4 with hStream tail5
          injection tail5 with hTransport tail6
          injection tail6 with hHistory tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hNameRow _
          subst hFamily
          subst hPointwise
          subst hBaire
          subst hNorm
          subst hRegseq
          subst hStream
          subst hTransport
          subst hHistory
          subst hReplay
          subst hProvenance
          subst hNameRow
          rfl

instance uniformBoundednessBHistCarrier : BHistCarrier UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformBoundednessToEventFlow
  fromEventFlow := uniformBoundednessFromEventFlow

instance uniformBoundednessChapterTasteGate : ChapterTasteGate UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x
    exact UniformBoundednessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformBoundednessToEventFlow_injective heq)

instance uniformBoundednessFieldFaithful : FieldFaithful UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformBoundednessFields
  field_faithful := UniformBoundednessTasteGate_single_carrier_alignment_fields

instance uniformBoundednessNontrivial : Nontrivial UniformBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformBoundednessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformBoundednessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformBoundednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformBoundednessChapterTasteGate

theorem UniformBoundednessTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformBoundednessDecodeBHist (uniformBoundednessEncodeBHist h) = h) ∧
      (∀ x : UniformBoundednessUp,
        uniformBoundednessFromEventFlow (uniformBoundednessToEventFlow x) = some x) ∧
        (∀ x y : UniformBoundednessUp,
          uniformBoundednessToEventFlow x = uniformBoundednessToEventFlow y → x = y) ∧
          uniformBoundednessEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : UniformBoundednessUp, uniformBoundednessFields x =
              uniformBoundednessFields y → x = y) ∧
              (∃ x y : UniformBoundednessUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformBoundednessTasteGate_single_carrier_alignment_decode,
      UniformBoundednessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => uniformBoundednessToEventFlow_injective heq),
      rfl,
      UniformBoundednessTasteGate_single_carrier_alignment_fields,
      ⟨UniformBoundednessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        UniformBoundednessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.UniformBoundednessUp.TasteGate
