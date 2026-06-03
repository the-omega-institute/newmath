import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEntourageBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformEntourageBasisUp : Type where
  | mk (R M U S F W Q H C P N : BHist) : RealUniformEntourageBasisUp
  deriving DecidableEq

def realUniformEntourageBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEntourageBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEntourageBasisEncodeBHist h

def realUniformEntourageBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEntourageBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEntourageBasisDecodeBHist tail)

private theorem RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformEntourageBasisFields : RealUniformEntourageBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEntourageBasisUp.mk R M U S F W Q H C P N =>
      [R, M, U, S, F, W, Q, H, C, P, N]

def realUniformEntourageBasisToEventFlow : RealUniformEntourageBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realUniformEntourageBasisFields x).map realUniformEntourageBasisEncodeBHist

def realUniformEntourageBasisFromEventFlow : EventFlow → Option RealUniformEntourageBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _R :: [] => none
  | _R :: _M :: [] => none
  | _R :: _M :: _U :: [] => none
  | _R :: _M :: _U :: _S :: [] => none
  | _R :: _M :: _U :: _S :: _F :: [] => none
  | _R :: _M :: _U :: _S :: _F :: _W :: [] => none
  | _R :: _M :: _U :: _S :: _F :: _W :: _Q :: [] => none
  | _R :: _M :: _U :: _S :: _F :: _W :: _Q :: _H :: [] => none
  | _R :: _M :: _U :: _S :: _F :: _W :: _Q :: _H :: _C :: [] => none
  | _R :: _M :: _U :: _S :: _F :: _W :: _Q :: _H :: _C :: _P :: [] => none
  | R :: M :: U :: S :: F :: W :: Q :: H :: C :: P :: N :: [] =>
      some
        (RealUniformEntourageBasisUp.mk
          (realUniformEntourageBasisDecodeBHist R)
          (realUniformEntourageBasisDecodeBHist M)
          (realUniformEntourageBasisDecodeBHist U)
          (realUniformEntourageBasisDecodeBHist S)
          (realUniformEntourageBasisDecodeBHist F)
          (realUniformEntourageBasisDecodeBHist W)
          (realUniformEntourageBasisDecodeBHist Q)
          (realUniformEntourageBasisDecodeBHist H)
          (realUniformEntourageBasisDecodeBHist C)
          (realUniformEntourageBasisDecodeBHist P)
          (realUniformEntourageBasisDecodeBHist N))
  | _R :: _M :: _U :: _S :: _F :: _W :: _Q :: _H :: _C :: _P :: _N ::
      _extra :: _rest => none

private theorem RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealUniformEntourageBasisUp,
      realUniformEntourageBasisFromEventFlow
          (realUniformEntourageBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M U S F W Q H C P N =>
      change
        some
          (RealUniformEntourageBasisUp.mk
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist R))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist M))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist U))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist S))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist F))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist W))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist Q))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist H))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist C))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist P))
            (realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist N))) =
          some (RealUniformEntourageBasisUp.mk R M U S F W Q H C P N)
      rw [RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode R,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode M,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode U,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode S,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode F,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode W,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode Q,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode H,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode C,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode P,
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode N]

private theorem RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformEntourageBasisUp} :
    realUniformEntourageBasisToEventFlow x = realUniformEntourageBasisToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEntourageBasisFromEventFlow (realUniformEntourageBasisToEventFlow x) =
        realUniformEntourageBasisFromEventFlow (realUniformEntourageBasisToEventFlow y) :=
    congrArg realUniformEntourageBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealUniformEntourageBasisUp,
      realUniformEntourageBasisFields x = realUniformEntourageBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 M1 U1 S1 F1 W1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 M2 U2 S2 F2 W2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realUniformEntourageBasisBHistCarrier :
    BHistCarrier RealUniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEntourageBasisToEventFlow
  fromEventFlow := realUniformEntourageBasisFromEventFlow

instance realUniformEntourageBasisChapterTasteGate :
    ChapterTasteGate RealUniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realUniformEntourageBasisFromEventFlow
        (realUniformEntourageBasisToEventFlow x) = some x
    exact RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realUniformEntourageBasisFieldFaithful :
    FieldFaithful RealUniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformEntourageBasisFields
  field_faithful := RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_fields

instance realUniformEntourageBasisNontrivial : Nontrivial RealUniformEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformEntourageBasisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformEntourageBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformEntourageBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformEntourageBasisChapterTasteGate

theorem RealUniformEntourageBasisUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realUniformEntourageBasisDecodeBHist (realUniformEntourageBasisEncodeBHist h) = h) ∧
      (∀ x : RealUniformEntourageBasisUp,
        realUniformEntourageBasisFromEventFlow
          (realUniformEntourageBasisToEventFlow x) = some x) ∧
        (∀ x y : RealUniformEntourageBasisUp,
          realUniformEntourageBasisToEventFlow x = realUniformEntourageBasisToEventFlow y →
            x = y) ∧
          realUniformEntourageBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_decode,
      RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealUniformEntourageBasisUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealUniformEntourageBasisUp
