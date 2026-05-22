import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteEpsilonNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteEpsilonNetUp : Type where
  | mk (X epsilon P C D H R S N : BHist) : FiniteEpsilonNetUp
  deriving DecidableEq

def finiteEpsilonNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteEpsilonNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteEpsilonNetEncodeBHist h

def finiteEpsilonNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteEpsilonNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteEpsilonNetDecodeBHist tail)

private theorem FiniteEpsilonNetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteEpsilonNetFields : FiniteEpsilonNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteEpsilonNetUp.mk X epsilon P C D H R S N => [X, epsilon, P, C, D, H, R, S, N]

def finiteEpsilonNetToEventFlow : FiniteEpsilonNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteEpsilonNetFields x).map finiteEpsilonNetEncodeBHist

def finiteEpsilonNetFromEventFlow : EventFlow → Option FiniteEpsilonNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _epsilon :: [] => none
  | _X :: _epsilon :: _P :: [] => none
  | _X :: _epsilon :: _P :: _C :: [] => none
  | _X :: _epsilon :: _P :: _C :: _D :: [] => none
  | _X :: _epsilon :: _P :: _C :: _D :: _H :: [] => none
  | _X :: _epsilon :: _P :: _C :: _D :: _H :: _R :: [] => none
  | _X :: _epsilon :: _P :: _C :: _D :: _H :: _R :: _S :: [] => none
  | X :: epsilon :: P :: C :: D :: H :: R :: S :: N :: [] =>
      some
        (FiniteEpsilonNetUp.mk
          (finiteEpsilonNetDecodeBHist X)
          (finiteEpsilonNetDecodeBHist epsilon)
          (finiteEpsilonNetDecodeBHist P)
          (finiteEpsilonNetDecodeBHist C)
          (finiteEpsilonNetDecodeBHist D)
          (finiteEpsilonNetDecodeBHist H)
          (finiteEpsilonNetDecodeBHist R)
          (finiteEpsilonNetDecodeBHist S)
          (finiteEpsilonNetDecodeBHist N))
  | _X :: _epsilon :: _P :: _C :: _D :: _H :: _R :: _S :: _N :: _extra :: _rest => none

private theorem FiniteEpsilonNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteEpsilonNetUp,
      finiteEpsilonNetFromEventFlow (finiteEpsilonNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X epsilon P C D H R S N =>
      change
        some
          (FiniteEpsilonNetUp.mk
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist X))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist epsilon))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist P))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist C))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist D))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist H))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist R))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist S))
            (finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist N))) =
          some (FiniteEpsilonNetUp.mk X epsilon P C D H R S N)
      rw [FiniteEpsilonNetTasteGate_single_carrier_alignment_decode X,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode epsilon,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode P,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode C,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode D,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode H,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode R,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode S,
        FiniteEpsilonNetTasteGate_single_carrier_alignment_decode N]

private theorem FiniteEpsilonNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteEpsilonNetUp} :
    finiteEpsilonNetToEventFlow x = finiteEpsilonNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteEpsilonNetFromEventFlow (finiteEpsilonNetToEventFlow x) =
        finiteEpsilonNetFromEventFlow (finiteEpsilonNetToEventFlow y) :=
    congrArg finiteEpsilonNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteEpsilonNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteEpsilonNetTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteEpsilonNetTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteEpsilonNetUp, finiteEpsilonNetFields x = finiteEpsilonNetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 epsilon1 P1 C1 D1 H1 R1 S1 N1 =>
      cases y with
      | mk X2 epsilon2 P2 C2 D2 H2 R2 S2 N2 =>
          cases hfields
          rfl

instance finiteEpsilonNetBHistCarrier : BHistCarrier FiniteEpsilonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteEpsilonNetToEventFlow
  fromEventFlow := finiteEpsilonNetFromEventFlow

instance finiteEpsilonNetChapterTasteGate : ChapterTasteGate FiniteEpsilonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteEpsilonNetFromEventFlow (finiteEpsilonNetToEventFlow x) = some x
    exact FiniteEpsilonNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteEpsilonNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteEpsilonNetFieldFaithful : FieldFaithful FiniteEpsilonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteEpsilonNetFields
  field_faithful := FiniteEpsilonNetTasteGate_single_carrier_alignment_fields

instance finiteEpsilonNetNontrivial : Nontrivial FiniteEpsilonNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteEpsilonNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteEpsilonNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteEpsilonNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteEpsilonNetChapterTasteGate

theorem FiniteEpsilonNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteEpsilonNetDecodeBHist (finiteEpsilonNetEncodeBHist h) = h) ∧
      (∀ x : FiniteEpsilonNetUp,
        finiteEpsilonNetFromEventFlow (finiteEpsilonNetToEventFlow x) = some x) ∧
        (∀ x y : FiniteEpsilonNetUp,
          finiteEpsilonNetToEventFlow x = finiteEpsilonNetToEventFlow y → x = y) ∧
          finiteEpsilonNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FiniteEpsilonNetTasteGate_single_carrier_alignment_decode,
      FiniteEpsilonNetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteEpsilonNetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteEpsilonNetUp
