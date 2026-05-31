import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ParacompactUp

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

private theorem ParacompactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, paracompactDecodeBHist (paracompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def paracompactFields : ParacompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ParacompactUp.mk T A R L N M H C P Z => [T, A, R, L, N, M, H, C, P, Z]

def paracompactToEventFlow : ParacompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (paracompactFields x).map paracompactEncodeBHist

private def paracompactEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => paracompactEventAt index rest

def paracompactFromEventFlow (ef : EventFlow) : Option ParacompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ParacompactUp.mk
      (paracompactDecodeBHist (paracompactEventAt 0 ef))
      (paracompactDecodeBHist (paracompactEventAt 1 ef))
      (paracompactDecodeBHist (paracompactEventAt 2 ef))
      (paracompactDecodeBHist (paracompactEventAt 3 ef))
      (paracompactDecodeBHist (paracompactEventAt 4 ef))
      (paracompactDecodeBHist (paracompactEventAt 5 ef))
      (paracompactDecodeBHist (paracompactEventAt 6 ef))
      (paracompactDecodeBHist (paracompactEventAt 7 ef))
      (paracompactDecodeBHist (paracompactEventAt 8 ef))
      (paracompactDecodeBHist (paracompactEventAt 9 ef)))

private theorem ParacompactTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ParacompactUp,
      paracompactFromEventFlow (paracompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
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
      rw [ParacompactTasteGate_single_carrier_alignment_decode_encode T,
        ParacompactTasteGate_single_carrier_alignment_decode_encode A,
        ParacompactTasteGate_single_carrier_alignment_decode_encode R,
        ParacompactTasteGate_single_carrier_alignment_decode_encode L,
        ParacompactTasteGate_single_carrier_alignment_decode_encode N,
        ParacompactTasteGate_single_carrier_alignment_decode_encode M,
        ParacompactTasteGate_single_carrier_alignment_decode_encode H,
        ParacompactTasteGate_single_carrier_alignment_decode_encode C,
        ParacompactTasteGate_single_carrier_alignment_decode_encode P,
        ParacompactTasteGate_single_carrier_alignment_decode_encode Z]

private theorem ParacompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ParacompactUp} :
    paracompactToEventFlow x = paracompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      paracompactFromEventFlow (paracompactToEventFlow x) =
        paracompactFromEventFlow (paracompactToEventFlow y) :=
    congrArg paracompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ParacompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ParacompactTasteGate_single_carrier_alignment_round_trip y)))

private theorem ParacompactTasteGate_single_carrier_alignment_fields :
    ∀ x y : ParacompactUp, paracompactFields x = paracompactFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 A1 R1 L1 N1 M1 H1 C1 P1 Z1 =>
      cases y with
      | mk T2 A2 R2 L2 N2 M2 H2 C2 P2 Z2 =>
          cases hfields
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
  field_faithful := ParacompactTasteGate_single_carrier_alignment_fields

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
      (∀ x : ParacompactUp,
        paracompactFromEventFlow (paracompactToEventFlow x) = some x) ∧
        (∀ x y : ParacompactUp,
          paracompactToEventFlow x = paracompactToEventFlow y → x = y) ∧
          paracompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨ParacompactTasteGate_single_carrier_alignment_decode_encode,
      ParacompactTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ParacompactTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ParacompactUp
