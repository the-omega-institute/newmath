import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ParacompactUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ParacompactUp : Type where
  | mk (T A R L N M H C P Z : BHist) : ParacompactUp
  deriving DecidableEq

def paracompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: paracompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: paracompactEncodeBHist h

def paracompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (paracompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (paracompactDecodeBHist tail)

private theorem paracompact_decode_encode :
    ∀ h : BHist, paracompactDecodeBHist (paracompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def paracompactFields : ParacompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ParacompactUp.mk T A R L N M H C P Z => [T, A, R, L, N, M, H, C, P, Z]

def paracompactToEventFlow : ParacompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (paracompactFields x).map paracompactEncodeBHist

private def ParacompactTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ParacompactTasteGate_single_carrier_alignment_eventAt index rest

def paracompactFromEventFlow (ef : EventFlow) : Option ParacompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ParacompactUp.mk
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 0 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 1 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 2 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 3 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 4 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 5 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 6 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 7 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 8 ef))
      (paracompactDecodeBHist (ParacompactTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem ParacompactTasteGate_single_carrier_alignment_round_trip
    (x : ParacompactUp) :
    paracompactFromEventFlow (paracompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T A R L N M H C P Z =>
      change
        some
            (ParacompactUp.mk
              (paracompactDecodeBHist (paracompactEncodeBHist T))
              (paracompactDecodeBHist (paracompactEncodeBHist A))
              (paracompactDecodeBHist (paracompactEncodeBHist R))
              (paracompactDecodeBHist (paracompactEncodeBHist L))
              (paracompactDecodeBHist (paracompactEncodeBHist N))
              (paracompactDecodeBHist (paracompactEncodeBHist M))
              (paracompactDecodeBHist (paracompactEncodeBHist H))
              (paracompactDecodeBHist (paracompactEncodeBHist C))
              (paracompactDecodeBHist (paracompactEncodeBHist P))
              (paracompactDecodeBHist (paracompactEncodeBHist Z))) =
          some (ParacompactUp.mk T A R L N M H C P Z)
      rw [paracompact_decode_encode T,
        paracompact_decode_encode A,
        paracompact_decode_encode R,
        paracompact_decode_encode L,
        paracompact_decode_encode N,
        paracompact_decode_encode M,
        paracompact_decode_encode H,
        paracompact_decode_encode C,
        paracompact_decode_encode P,
        paracompact_decode_encode Z]

private theorem ParacompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ParacompactUp} :
    paracompactToEventFlow x = paracompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = paracompactFromEventFlow (paracompactToEventFlow x) :=
        (ParacompactTasteGate_single_carrier_alignment_round_trip x).symm
      _ = paracompactFromEventFlow (paracompactToEventFlow y) :=
        congrArg paracompactFromEventFlow hxy
      _ = some y := ParacompactTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem paracompact_field_faithful :
    ∀ x y : ParacompactUp, paracompactFields x = paracompactFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ A₁ R₁ L₁ N₁ M₁ H₁ C₁ P₁ Z₁ =>
      cases y with
      | mk T₂ A₂ R₂ L₂ N₂ M₂ H₂ C₂ P₂ Z₂ =>
          injection hfields with hT tail0
          injection tail0 with hA tail1
          injection tail1 with hR tail2
          injection tail2 with hL tail3
          injection tail3 with hN tail4
          injection tail4 with hM tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hZ _
          subst hT
          subst hA
          subst hR
          subst hL
          subst hN
          subst hM
          subst hH
          subst hC
          subst hP
          subst hZ
          rfl

instance paracompactBHistCarrier : BHistCarrier ParacompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := paracompactToEventFlow
  fromEventFlow := paracompactFromEventFlow

instance paracompactChapterTasteGate : ChapterTasteGate ParacompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change paracompactFromEventFlow (paracompactToEventFlow x) = some x
    exact ParacompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ParacompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance paracompactFieldFaithful : FieldFaithful ParacompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := paracompactFields
  field_faithful := paracompact_field_faithful

instance paracompactNontrivial : BEDC.Meta.TasteGate.Nontrivial ParacompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ParacompactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ParacompactUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ParacompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  paracompactChapterTasteGate

theorem ParacompactTasteGate_single_carrier_alignment :
    (∀ h : BHist, paracompactDecodeBHist (paracompactEncodeBHist h) = h) ∧
      (∀ x : ParacompactUp, paracompactFromEventFlow (paracompactToEventFlow x) = some x) ∧
        (∀ x y : ParacompactUp, paracompactToEventFlow x = paracompactToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate ParacompactUp) ∧
            (∀ x y : ParacompactUp, paracompactFields x = paracompactFields y → x = y) ∧
              (∀ x : ParacompactUp, ∃ h : BHist, List.Mem h (paracompactFields x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨paracompact_decode_encode,
      ParacompactTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => ParacompactTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      ⟨paracompactChapterTasteGate⟩,
      paracompact_field_faithful,
      by
        intro x
        cases x with
        | mk T A R L N M H C P Z =>
            exact ⟨T, List.Mem.head _⟩⟩

end BEDC.Derived.ParacompactUp.TasteGate
