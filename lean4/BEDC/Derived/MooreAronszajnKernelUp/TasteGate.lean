import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreAronszajnKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreAronszajnKernelUp : Type where
  | mk (K0 G V H M R C P N : BHist) : MooreAronszajnKernelUp
  deriving DecidableEq

def mooreAronszajnKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreAronszajnKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreAronszajnKernelEncodeBHist h

def mooreAronszajnKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreAronszajnKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreAronszajnKernelDecodeBHist tail)

private theorem mooreAronszajnKernelDecode_encode :
    ∀ h : BHist, mooreAronszajnKernelDecodeBHist
      (mooreAronszajnKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def mooreAronszajnKernelEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mooreAronszajnKernelEventAtDefault index rest

def mooreAronszajnKernelFields : MooreAronszajnKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreAronszajnKernelUp.mk K0 G V H M R C P N => [K0, G, V, H, M, R, C, P, N]

def mooreAronszajnKernelToEventFlow : MooreAronszajnKernelUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (mooreAronszajnKernelFields x).map mooreAronszajnKernelEncodeBHist

def mooreAronszajnKernelFromEventFlow
    (ef : EventFlow) : Option MooreAronszajnKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MooreAronszajnKernelUp.mk
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 0 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 1 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 2 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 3 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 4 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 5 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 6 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 7 ef))
      (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEventAtDefault 8 ef)))

private theorem MooreAronszajnKernelUp_round_trip (x : MooreAronszajnKernelUp) :
    mooreAronszajnKernelFromEventFlow (mooreAronszajnKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K0 G V H M R C P N =>
      change
        some
          (MooreAronszajnKernelUp.mk
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist K0))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist G))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist V))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist H))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist M))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist R))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist C))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist P))
            (mooreAronszajnKernelDecodeBHist (mooreAronszajnKernelEncodeBHist N))) =
          some (MooreAronszajnKernelUp.mk K0 G V H M R C P N)
      rw [mooreAronszajnKernelDecode_encode K0, mooreAronszajnKernelDecode_encode G,
        mooreAronszajnKernelDecode_encode V, mooreAronszajnKernelDecode_encode H,
        mooreAronszajnKernelDecode_encode M, mooreAronszajnKernelDecode_encode R,
        mooreAronszajnKernelDecode_encode C, mooreAronszajnKernelDecode_encode P,
        mooreAronszajnKernelDecode_encode N]

private theorem MooreAronszajnKernelUp_toEventFlow_injective
    {x y : MooreAronszajnKernelUp} :
    mooreAronszajnKernelToEventFlow x = mooreAronszajnKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreAronszajnKernelFromEventFlow (mooreAronszajnKernelToEventFlow x) =
        mooreAronszajnKernelFromEventFlow (mooreAronszajnKernelToEventFlow y) :=
    congrArg mooreAronszajnKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MooreAronszajnKernelUp_round_trip x).symm
      (Eq.trans hread (MooreAronszajnKernelUp_round_trip y)))

private theorem MooreAronszajnKernelUp_fields_faithful :
    ∀ x y : MooreAronszajnKernelUp,
      mooreAronszajnKernelFields x = mooreAronszajnKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K01 G1 V1 H1 M1 R1 C1 P1 N1 =>
      cases y with
      | mk K02 G2 V2 H2 M2 R2 C2 P2 N2 =>
          cases hfields
          rfl

instance mooreAronszajnKernelBHistCarrier : BHistCarrier MooreAronszajnKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreAronszajnKernelToEventFlow
  fromEventFlow := mooreAronszajnKernelFromEventFlow

instance mooreAronszajnKernelChapterTasteGate :
    ChapterTasteGate MooreAronszajnKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreAronszajnKernelFromEventFlow (mooreAronszajnKernelToEventFlow x) = some x
    exact MooreAronszajnKernelUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreAronszajnKernelUp_toEventFlow_injective heq)

instance mooreAronszajnKernelFieldFaithful :
    FieldFaithful MooreAronszajnKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mooreAronszajnKernelFields
  field_faithful := MooreAronszajnKernelUp_fields_faithful

instance mooreAronszajnKernelNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MooreAronszajnKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MooreAronszajnKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MooreAronszajnKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MooreAronszajnKernelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MooreAronszajnKernelUp) ∧
      (∀ x : MooreAronszajnKernelUp,
        ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
        mooreAronszajnKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨mooreAronszajnKernelChapterTasteGate⟩
  · constructor
    · intro x
      exact ⟨BHistCarrier.toEventFlow x, ChapterTasteGate.round_trip x⟩
    · rfl

end BEDC.Derived.MooreAronszajnKernelUp
