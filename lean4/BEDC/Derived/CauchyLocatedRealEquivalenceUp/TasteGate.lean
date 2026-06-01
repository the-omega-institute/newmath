import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLocatedRealEquivalenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLocatedRealEquivalenceUp : Type where
  | mk (C L U W R D E H Ct P N : BHist) : CauchyLocatedRealEquivalenceUp
  deriving DecidableEq

def cauchyLocatedRealEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyLocatedRealEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyLocatedRealEquivalenceEncodeBHist h

def cauchyLocatedRealEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLocatedRealEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLocatedRealEquivalenceDecodeBHist tail)

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyLocatedRealEquivalenceDecodeBHist
          (cauchyLocatedRealEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyLocatedRealEquivalenceFields :
    CauchyLocatedRealEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyLocatedRealEquivalenceUp.mk C L U W R D E H Ct P N =>
      [C, L, U, W, R, D, E, H, Ct, P, N]

def cauchyLocatedRealEquivalenceToEventFlow :
    CauchyLocatedRealEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyLocatedRealEquivalenceFields x).map
      cauchyLocatedRealEquivalenceEncodeBHist

private def cauchyLocatedRealEquivalenceEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyLocatedRealEquivalenceEventAt index rest

def cauchyLocatedRealEquivalenceFromEventFlow
    (ef : EventFlow) : Option CauchyLocatedRealEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyLocatedRealEquivalenceUp.mk
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 0 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 1 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 2 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 3 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 4 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 5 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 6 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 7 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 8 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 9 ef))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceEventAt 10 ef)))

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip
    (x : CauchyLocatedRealEquivalenceUp) :
    cauchyLocatedRealEquivalenceFromEventFlow
        (cauchyLocatedRealEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C L U W R D E H Ct P N =>
      change
        some
          (CauchyLocatedRealEquivalenceUp.mk
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist C))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist L))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist U))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist W))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist R))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist D))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist E))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist H))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist Ct))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist P))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (cauchyLocatedRealEquivalenceEncodeBHist N))) =
          some (CauchyLocatedRealEquivalenceUp.mk C L U W R D E H Ct P N)
      rw [CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode C,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode L,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode U,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode W,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode R,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode D,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode E,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode H,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode Ct,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode P,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode N]

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_injective
    {x y : CauchyLocatedRealEquivalenceUp} :
    cauchyLocatedRealEquivalenceToEventFlow x =
      cauchyLocatedRealEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyLocatedRealEquivalenceFromEventFlow
          (cauchyLocatedRealEquivalenceToEventFlow x) =
        cauchyLocatedRealEquivalenceFromEventFlow
          (cauchyLocatedRealEquivalenceToEventFlow y) :=
    congrArg cauchyLocatedRealEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyLocatedRealEquivalenceUp,
      cauchyLocatedRealEquivalenceFields x =
        cauchyLocatedRealEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ L₁ U₁ W₁ R₁ D₁ E₁ H₁ Ct₁ P₁ N₁ =>
      cases y with
      | mk C₂ L₂ U₂ W₂ R₂ D₂ E₂ H₂ Ct₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyLocatedRealEquivalenceBHistCarrier :
    BHistCarrier CauchyLocatedRealEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyLocatedRealEquivalenceToEventFlow
  fromEventFlow := cauchyLocatedRealEquivalenceFromEventFlow

instance cauchyLocatedRealEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyLocatedRealEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyLocatedRealEquivalenceFromEventFlow
          (cauchyLocatedRealEquivalenceToEventFlow x) = some x
    exact CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_injective heq)

instance cauchyLocatedRealEquivalenceFieldFaithful :
    FieldFaithful CauchyLocatedRealEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyLocatedRealEquivalenceFields
  field_faithful :=
    CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_fields

instance cauchyLocatedRealEquivalenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyLocatedRealEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyLocatedRealEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyLocatedRealEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyLocatedRealEquivalenceUp) ∧
      (∀ x : CauchyLocatedRealEquivalenceUp,
        ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
        ∃ x y : CauchyLocatedRealEquivalenceUp,
          x ≠ y ∧
            FieldFaithful.fields x =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty] ∧
              FieldFaithful.fields y =
                [BHist.e0 BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                  BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                  BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact ⟨cauchyLocatedRealEquivalenceChapterTasteGate⟩
  · constructor
    · intro x
      exact ChapterTasteGate.no_hidden_input x
    · refine
        ⟨CauchyLocatedRealEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty,
          CauchyLocatedRealEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty, ?_, ?_, ?_⟩
      · intro h
        cases h
      · rfl
      · rfl

end BEDC.Derived.CauchyLocatedRealEquivalenceUp.TasteGate
