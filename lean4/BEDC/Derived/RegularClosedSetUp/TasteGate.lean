import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularClosedSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularClosedSetUp : Type where
  | mk (T S O I C E H Q P N : BHist) : RegularClosedSetUp
  deriving DecidableEq

def regularClosedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularClosedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularClosedSetEncodeBHist h

def regularClosedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularClosedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularClosedSetDecodeBHist tail)

private theorem RegularClosedSetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularClosedSetDecodeBHist (regularClosedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularClosedSetFields : RegularClosedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularClosedSetUp.mk T S O I C E H Q P N => [T, S, O, I, C, E, H, Q, P, N]

def regularClosedSetToEventFlow : RegularClosedSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularClosedSetFields x).map regularClosedSetEncodeBHist

def regularClosedSetFromEventFlow : EventFlow → Option RegularClosedSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _T :: [] => none
  | _T :: _S :: [] => none
  | _T :: _S :: _O :: [] => none
  | _T :: _S :: _O :: _I :: [] => none
  | _T :: _S :: _O :: _I :: _C :: [] => none
  | _T :: _S :: _O :: _I :: _C :: _E :: [] => none
  | _T :: _S :: _O :: _I :: _C :: _E :: _H :: [] => none
  | _T :: _S :: _O :: _I :: _C :: _E :: _H :: _Q :: [] => none
  | _T :: _S :: _O :: _I :: _C :: _E :: _H :: _Q :: _P :: [] => none
  | T :: S :: O :: I :: C :: E :: H :: Q :: P :: N :: [] =>
      some
        (RegularClosedSetUp.mk
          (regularClosedSetDecodeBHist T)
          (regularClosedSetDecodeBHist S)
          (regularClosedSetDecodeBHist O)
          (regularClosedSetDecodeBHist I)
          (regularClosedSetDecodeBHist C)
          (regularClosedSetDecodeBHist E)
          (regularClosedSetDecodeBHist H)
          (regularClosedSetDecodeBHist Q)
          (regularClosedSetDecodeBHist P)
          (regularClosedSetDecodeBHist N))
  | _T :: _S :: _O :: _I :: _C :: _E :: _H :: _Q :: _P :: _N :: _extra :: _rest => none

private theorem RegularClosedSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularClosedSetUp,
      regularClosedSetFromEventFlow (regularClosedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S O I C E H Q P N =>
      change
        some
          (RegularClosedSetUp.mk
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist T))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist S))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist O))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist I))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist C))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist E))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist H))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist Q))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist P))
            (regularClosedSetDecodeBHist (regularClosedSetEncodeBHist N))) =
          some (RegularClosedSetUp.mk T S O I C E H Q P N)
      rw [RegularClosedSetTasteGate_single_carrier_alignment_decode T,
        RegularClosedSetTasteGate_single_carrier_alignment_decode S,
        RegularClosedSetTasteGate_single_carrier_alignment_decode O,
        RegularClosedSetTasteGate_single_carrier_alignment_decode I,
        RegularClosedSetTasteGate_single_carrier_alignment_decode C,
        RegularClosedSetTasteGate_single_carrier_alignment_decode E,
        RegularClosedSetTasteGate_single_carrier_alignment_decode H,
        RegularClosedSetTasteGate_single_carrier_alignment_decode Q,
        RegularClosedSetTasteGate_single_carrier_alignment_decode P,
        RegularClosedSetTasteGate_single_carrier_alignment_decode N]

private theorem RegularClosedSetToEventFlow_injective {x y : RegularClosedSetUp} :
    regularClosedSetToEventFlow x = regularClosedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularClosedSetFromEventFlow (regularClosedSetToEventFlow x) =
        regularClosedSetFromEventFlow (regularClosedSetToEventFlow y) :=
    congrArg regularClosedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularClosedSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularClosedSetTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularClosedSetTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularClosedSetUp, regularClosedSetFields x = regularClosedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 S1 O1 I1 C1 E1 H1 Q1 P1 N1 =>
      cases y with
      | mk T2 S2 O2 I2 C2 E2 H2 Q2 P2 N2 =>
          cases hfields
          rfl

instance regularClosedSetBHistCarrier : BHistCarrier RegularClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularClosedSetToEventFlow
  fromEventFlow := regularClosedSetFromEventFlow

instance regularClosedSetChapterTasteGate : ChapterTasteGate RegularClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularClosedSetFromEventFlow (regularClosedSetToEventFlow x) = some x
    exact RegularClosedSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularClosedSetToEventFlow_injective heq)

instance regularClosedSetFieldFaithful : FieldFaithful RegularClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularClosedSetFields
  field_faithful := RegularClosedSetTasteGate_single_carrier_alignment_fields

instance regularClosedSetNontrivial : Nontrivial RegularClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularClosedSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularClosedSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularClosedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularClosedSetChapterTasteGate

theorem RegularClosedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularClosedSetDecodeBHist (regularClosedSetEncodeBHist h) = h) ∧
      (∀ x : RegularClosedSetUp,
        regularClosedSetFromEventFlow (regularClosedSetToEventFlow x) = some x) ∧
        (∀ x y : RegularClosedSetUp,
          regularClosedSetToEventFlow x = regularClosedSetToEventFlow y → x = y) ∧
          regularClosedSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RegularClosedSetTasteGate_single_carrier_alignment_decode,
      RegularClosedSetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularClosedSetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularClosedSetUp
