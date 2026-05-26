import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicStepApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicStepApproximationUp : Type where
  | mk (I M L V O E H C P N : BHist) : DyadicStepApproximationUp
  deriving DecidableEq

def dyadicStepApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicStepApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicStepApproximationEncodeBHist h

def dyadicStepApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicStepApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicStepApproximationDecodeBHist tail)

private theorem DyadicStepApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicStepApproximationFields : DyadicStepApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicStepApproximationUp.mk I M L V O E H C P N => [I, M, L, V, O, E, H, C, P, N]

def dyadicStepApproximationToEventFlow : DyadicStepApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicStepApproximationFields x).map dyadicStepApproximationEncodeBHist

def dyadicStepApproximationFromEventFlow : EventFlow → Option DyadicStepApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _I :: [] => none
  | _I :: _M :: [] => none
  | _I :: _M :: _L :: [] => none
  | _I :: _M :: _L :: _V :: [] => none
  | _I :: _M :: _L :: _V :: _O :: [] => none
  | _I :: _M :: _L :: _V :: _O :: _E :: [] => none
  | _I :: _M :: _L :: _V :: _O :: _E :: _H :: [] => none
  | _I :: _M :: _L :: _V :: _O :: _E :: _H :: _C :: [] => none
  | _I :: _M :: _L :: _V :: _O :: _E :: _H :: _C :: _P :: [] => none
  | I :: M :: L :: V :: O :: E :: H :: C :: P :: N :: [] =>
      some
        (DyadicStepApproximationUp.mk
          (dyadicStepApproximationDecodeBHist I)
          (dyadicStepApproximationDecodeBHist M)
          (dyadicStepApproximationDecodeBHist L)
          (dyadicStepApproximationDecodeBHist V)
          (dyadicStepApproximationDecodeBHist O)
          (dyadicStepApproximationDecodeBHist E)
          (dyadicStepApproximationDecodeBHist H)
          (dyadicStepApproximationDecodeBHist C)
          (dyadicStepApproximationDecodeBHist P)
          (dyadicStepApproximationDecodeBHist N))
  | _I :: _M :: _L :: _V :: _O :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem DyadicStepApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicStepApproximationUp,
      dyadicStepApproximationFromEventFlow (dyadicStepApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M L V O E H C P N =>
      change
        some
          (DyadicStepApproximationUp.mk
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist I))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist M))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist L))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist V))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist O))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist E))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist H))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist C))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist P))
            (dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist N))) =
          some (DyadicStepApproximationUp.mk I M L V O E H C P N)
      rw [DyadicStepApproximationTasteGate_single_carrier_alignment_decode I,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode M,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode L,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode V,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode O,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode E,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode H,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode C,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode P,
        DyadicStepApproximationTasteGate_single_carrier_alignment_decode N]

private theorem DyadicStepApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicStepApproximationUp} :
    dyadicStepApproximationToEventFlow x = dyadicStepApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicStepApproximationFromEventFlow (dyadicStepApproximationToEventFlow x) =
        dyadicStepApproximationFromEventFlow (dyadicStepApproximationToEventFlow y) :=
    congrArg dyadicStepApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicStepApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicStepApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicStepApproximationTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicStepApproximationUp,
      dyadicStepApproximationFields x = dyadicStepApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 M1 L1 V1 O1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 L2 V2 O2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicStepApproximationBHistCarrier : BHistCarrier DyadicStepApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicStepApproximationToEventFlow
  fromEventFlow := dyadicStepApproximationFromEventFlow

instance dyadicStepApproximationChapterTasteGate :
    ChapterTasteGate DyadicStepApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicStepApproximationFromEventFlow (dyadicStepApproximationToEventFlow x) = some x
    exact DyadicStepApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicStepApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicStepApproximationFieldFaithful :
    FieldFaithful DyadicStepApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicStepApproximationFields
  field_faithful := DyadicStepApproximationTasteGate_single_carrier_alignment_fields

instance dyadicStepApproximationNontrivial : Nontrivial DyadicStepApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicStepApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicStepApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicStepApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicStepApproximationChapterTasteGate

theorem DyadicStepApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicStepApproximationDecodeBHist (dyadicStepApproximationEncodeBHist h) = h) ∧
      (∀ x : DyadicStepApproximationUp,
        dyadicStepApproximationFromEventFlow (dyadicStepApproximationToEventFlow x) = some x) ∧
        (∀ x y : DyadicStepApproximationUp,
          dyadicStepApproximationToEventFlow x = dyadicStepApproximationToEventFlow y → x = y) ∧
          dyadicStepApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DyadicStepApproximationTasteGate_single_carrier_alignment_decode,
      DyadicStepApproximationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicStepApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicStepApproximationUp
