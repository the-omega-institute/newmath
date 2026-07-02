import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PeanoKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PeanoKernelUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (I M A Q S R W D E H C P N : BHist) : PeanoKernelUp
  deriving DecidableEq

def peanoKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: peanoKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: peanoKernelEncodeBHist h

def peanoKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (peanoKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (peanoKernelDecodeBHist tail)

private theorem PeanoKernelTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, peanoKernelDecodeBHist (peanoKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def peanoKernelFields : PeanoKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PeanoKernelUp.mk I M A Q S R W D E H C P N => [I, M, A, Q, S, R, W, D, E, H, C, P, N]

def peanoKernelToEventFlow : PeanoKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (peanoKernelFields x).map peanoKernelEncodeBHist

def peanoKernelFromEventFlow : EventFlow → Option PeanoKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [I, M, A, Q, S, R, W, D, E, H, C, P, N] =>
      some
        (PeanoKernelUp.mk
          (peanoKernelDecodeBHist I)
          (peanoKernelDecodeBHist M)
          (peanoKernelDecodeBHist A)
          (peanoKernelDecodeBHist Q)
          (peanoKernelDecodeBHist S)
          (peanoKernelDecodeBHist R)
          (peanoKernelDecodeBHist W)
          (peanoKernelDecodeBHist D)
          (peanoKernelDecodeBHist E)
          (peanoKernelDecodeBHist H)
          (peanoKernelDecodeBHist C)
          (peanoKernelDecodeBHist P)
          (peanoKernelDecodeBHist N))
  | _ => none

private theorem PeanoKernelTasteGate_single_carrier_alignment_round_trip
    (x : PeanoKernelUp) :
    peanoKernelFromEventFlow (peanoKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I M A Q S R W D E H C P N =>
      change
        some
          (PeanoKernelUp.mk
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist I))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist M))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist A))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist Q))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist S))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist R))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist W))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist D))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist E))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist H))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist C))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist P))
            (peanoKernelDecodeBHist (peanoKernelEncodeBHist N))) =
          some (PeanoKernelUp.mk I M A Q S R W D E H C P N)
      rw [PeanoKernelTasteGate_single_carrier_alignment_decode I,
        PeanoKernelTasteGate_single_carrier_alignment_decode M,
        PeanoKernelTasteGate_single_carrier_alignment_decode A,
        PeanoKernelTasteGate_single_carrier_alignment_decode Q,
        PeanoKernelTasteGate_single_carrier_alignment_decode S,
        PeanoKernelTasteGate_single_carrier_alignment_decode R,
        PeanoKernelTasteGate_single_carrier_alignment_decode W,
        PeanoKernelTasteGate_single_carrier_alignment_decode D,
        PeanoKernelTasteGate_single_carrier_alignment_decode E,
        PeanoKernelTasteGate_single_carrier_alignment_decode H,
        PeanoKernelTasteGate_single_carrier_alignment_decode C,
        PeanoKernelTasteGate_single_carrier_alignment_decode P,
        PeanoKernelTasteGate_single_carrier_alignment_decode N]

private theorem PeanoKernelTasteGate_single_carrier_alignment_injective
    {x y : PeanoKernelUp} :
    peanoKernelToEventFlow x = peanoKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      peanoKernelFromEventFlow (peanoKernelToEventFlow x) =
        peanoKernelFromEventFlow (peanoKernelToEventFlow y) :=
    congrArg peanoKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PeanoKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PeanoKernelTasteGate_single_carrier_alignment_round_trip y)))

private theorem PeanoKernelTasteGate_single_carrier_alignment_fields
    (x y : PeanoKernelUp) :
    peanoKernelFields x = peanoKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk I1 M1 A1 Q1 S1 R1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 A2 Q2 S2 R2 W2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance peanoKernelBHistCarrier : BHistCarrier PeanoKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := peanoKernelToEventFlow
  fromEventFlow := peanoKernelFromEventFlow

instance peanoKernelChapterTasteGate : ChapterTasteGate PeanoKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change peanoKernelFromEventFlow (peanoKernelToEventFlow x) = some x
    exact PeanoKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PeanoKernelTasteGate_single_carrier_alignment_injective heq)

instance peanoKernelFieldFaithful : FieldFaithful PeanoKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := peanoKernelFields
  field_faithful := PeanoKernelTasteGate_single_carrier_alignment_fields

instance peanoKernelNontrivial : Nontrivial PeanoKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PeanoKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PeanoKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PeanoKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  peanoKernelChapterTasteGate

theorem PeanoKernelTasteGate_single_carrier_alignment :
    (∀ h : BHist, peanoKernelDecodeBHist (peanoKernelEncodeBHist h) = h) ∧
      (∀ x : PeanoKernelUp, peanoKernelFromEventFlow (peanoKernelToEventFlow x) = some x) ∧
        (∀ x y : PeanoKernelUp, peanoKernelToEventFlow x = peanoKernelToEventFlow y → x = y) ∧
          peanoKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨PeanoKernelTasteGate_single_carrier_alignment_decode,
      PeanoKernelTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PeanoKernelTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.PeanoKernelUp
