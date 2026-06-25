import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HautusTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HautusTestUp : Type where
  | mk (X U Y A B C Lambda Pi Q O M V T R P N : BHist) : HautusTestUp
  deriving DecidableEq

def hautusTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hautusTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hautusTestEncodeBHist h

def hautusTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hautusTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hautusTestDecodeBHist tail)

private theorem HautusTestTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hautusTestDecodeBHist (hautusTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hautusTestFields : HautusTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HautusTestUp.mk X U Y A B C Lambda Pi Q O M V T R P N =>
      [X, U, Y, A, B, C, Lambda, Pi, Q, O, M, V, T, R, P, N]

def hautusTestToEventFlow : HautusTestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hautusTestFields x).map hautusTestEncodeBHist

def hautusTestFromEventFlow : EventFlow → Option HautusTestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _U :: [] => none
  | _X :: _U :: _Y :: [] => none
  | _X :: _U :: _Y :: _A :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: _M :: [] =>
      none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: _M :: _V ::
      [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: _M :: _V ::
      _T :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: _M :: _V ::
      _T :: _R :: [] => none
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: _M :: _V ::
      _T :: _R :: _P :: [] => none
  | X :: U :: Y :: A :: B :: C :: Lambda :: Pi :: Q :: O :: M :: V :: T :: R ::
      P :: N :: [] =>
      some
        (HautusTestUp.mk
          (hautusTestDecodeBHist X)
          (hautusTestDecodeBHist U)
          (hautusTestDecodeBHist Y)
          (hautusTestDecodeBHist A)
          (hautusTestDecodeBHist B)
          (hautusTestDecodeBHist C)
          (hautusTestDecodeBHist Lambda)
          (hautusTestDecodeBHist Pi)
          (hautusTestDecodeBHist Q)
          (hautusTestDecodeBHist O)
          (hautusTestDecodeBHist M)
          (hautusTestDecodeBHist V)
          (hautusTestDecodeBHist T)
          (hautusTestDecodeBHist R)
          (hautusTestDecodeBHist P)
          (hautusTestDecodeBHist N))
  | _X :: _U :: _Y :: _A :: _B :: _C :: _Lambda :: _Pi :: _Q :: _O :: _M :: _V ::
      _T :: _R :: _P :: _N :: _extra :: _rest => none

private theorem HautusTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HautusTestUp, hautusTestFromEventFlow (hautusTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U Y A B C Lambda Pi Q O M V T R P N =>
      change
        some
          (HautusTestUp.mk
            (hautusTestDecodeBHist (hautusTestEncodeBHist X))
            (hautusTestDecodeBHist (hautusTestEncodeBHist U))
            (hautusTestDecodeBHist (hautusTestEncodeBHist Y))
            (hautusTestDecodeBHist (hautusTestEncodeBHist A))
            (hautusTestDecodeBHist (hautusTestEncodeBHist B))
            (hautusTestDecodeBHist (hautusTestEncodeBHist C))
            (hautusTestDecodeBHist (hautusTestEncodeBHist Lambda))
            (hautusTestDecodeBHist (hautusTestEncodeBHist Pi))
            (hautusTestDecodeBHist (hautusTestEncodeBHist Q))
            (hautusTestDecodeBHist (hautusTestEncodeBHist O))
            (hautusTestDecodeBHist (hautusTestEncodeBHist M))
            (hautusTestDecodeBHist (hautusTestEncodeBHist V))
            (hautusTestDecodeBHist (hautusTestEncodeBHist T))
            (hautusTestDecodeBHist (hautusTestEncodeBHist R))
            (hautusTestDecodeBHist (hautusTestEncodeBHist P))
            (hautusTestDecodeBHist (hautusTestEncodeBHist N))) =
          some (HautusTestUp.mk X U Y A B C Lambda Pi Q O M V T R P N)
      rw [HautusTestTasteGate_single_carrier_alignment_decode X,
        HautusTestTasteGate_single_carrier_alignment_decode U,
        HautusTestTasteGate_single_carrier_alignment_decode Y,
        HautusTestTasteGate_single_carrier_alignment_decode A,
        HautusTestTasteGate_single_carrier_alignment_decode B,
        HautusTestTasteGate_single_carrier_alignment_decode C,
        HautusTestTasteGate_single_carrier_alignment_decode Lambda,
        HautusTestTasteGate_single_carrier_alignment_decode Pi,
        HautusTestTasteGate_single_carrier_alignment_decode Q,
        HautusTestTasteGate_single_carrier_alignment_decode O,
        HautusTestTasteGate_single_carrier_alignment_decode M,
        HautusTestTasteGate_single_carrier_alignment_decode V,
        HautusTestTasteGate_single_carrier_alignment_decode T,
        HautusTestTasteGate_single_carrier_alignment_decode R,
        HautusTestTasteGate_single_carrier_alignment_decode P,
        HautusTestTasteGate_single_carrier_alignment_decode N]

private theorem HautusTestToEventFlow_injective {x y : HautusTestUp} :
    hautusTestToEventFlow x = hautusTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hautusTestFromEventFlow (hautusTestToEventFlow x) =
        hautusTestFromEventFlow (hautusTestToEventFlow y) :=
    congrArg hautusTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HautusTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HautusTestTasteGate_single_carrier_alignment_round_trip y)))

private theorem HautusTestTasteGate_single_carrier_alignment_fields :
    ∀ x y : HautusTestUp, hautusTestFields x = hautusTestFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 U1 Y1 A1 B1 C1 Lambda1 Pi1 Q1 O1 M1 V1 T1 R1 P1 N1 =>
      cases y with
      | mk X2 U2 Y2 A2 B2 C2 Lambda2 Pi2 Q2 O2 M2 V2 T2 R2 P2 N2 =>
          cases hfields
          rfl

instance hautusTestBHistCarrier : BHistCarrier HautusTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hautusTestToEventFlow
  fromEventFlow := hautusTestFromEventFlow

instance hautusTestChapterTasteGate : ChapterTasteGate HautusTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hautusTestFromEventFlow (hautusTestToEventFlow x) = some x
    exact HautusTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HautusTestToEventFlow_injective heq)

instance hautusTestFieldFaithful : FieldFaithful HautusTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hautusTestFields
  field_faithful := HautusTestTasteGate_single_carrier_alignment_fields

instance hautusTestNontrivial : Nontrivial HautusTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HautusTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HautusTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HautusTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hautusTestChapterTasteGate

theorem HautusTestTasteGate_single_carrier_alignment :
    (∀ h : BHist, hautusTestDecodeBHist (hautusTestEncodeBHist h) = h) ∧
      (∀ x : HautusTestUp, hautusTestFromEventFlow (hautusTestToEventFlow x) = some x) ∧
        (∀ x y : HautusTestUp, hautusTestToEventFlow x = hautusTestToEventFlow y → x = y) ∧
          hautusTestEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨HautusTestTasteGate_single_carrier_alignment_decode,
      HautusTestTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HautusTestToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HautusTestUp
