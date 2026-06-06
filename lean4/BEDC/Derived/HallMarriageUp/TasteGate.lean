import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HallMarriageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HallMarriageUp : Type where
  | mk (L R E N S B A M U P C T Q : BHist) : HallMarriageUp
  deriving DecidableEq

def hallMarriageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hallMarriageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hallMarriageEncodeBHist h

def hallMarriageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hallMarriageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hallMarriageDecodeBHist tail)

private theorem HallMarriageTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hallMarriageDecodeBHist (hallMarriageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hallMarriageFields : HallMarriageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HallMarriageUp.mk L R E N S B A M U P C T Q => [L, R, E, N, S, B, A, M, U, P, C, T, Q]

def hallMarriageToEventFlow : HallMarriageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hallMarriageFields x).map hallMarriageEncodeBHist

def hallMarriageFromEventFlow : EventFlow → Option HallMarriageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _L :: [] => none
  | _L :: _R :: [] => none
  | _L :: _R :: _E :: [] => none
  | _L :: _R :: _E :: _N :: [] => none
  | _L :: _R :: _E :: _N :: _S :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: _M :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: _M :: _U :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: _M :: _U :: _P :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: _M :: _U :: _P :: _C :: [] => none
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: _M :: _U :: _P :: _C :: _T :: [] => none
  | L :: R :: E :: N :: S :: B :: A :: M :: U :: P :: C :: T :: Q :: [] =>
      some
        (HallMarriageUp.mk
          (hallMarriageDecodeBHist L)
          (hallMarriageDecodeBHist R)
          (hallMarriageDecodeBHist E)
          (hallMarriageDecodeBHist N)
          (hallMarriageDecodeBHist S)
          (hallMarriageDecodeBHist B)
          (hallMarriageDecodeBHist A)
          (hallMarriageDecodeBHist M)
          (hallMarriageDecodeBHist U)
          (hallMarriageDecodeBHist P)
          (hallMarriageDecodeBHist C)
          (hallMarriageDecodeBHist T)
          (hallMarriageDecodeBHist Q))
  | _L :: _R :: _E :: _N :: _S :: _B :: _A :: _M :: _U :: _P :: _C :: _T ::
      _Q :: _extra :: _rest => none

private theorem HallMarriageTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HallMarriageUp, hallMarriageFromEventFlow (hallMarriageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R E N S B A M U P C T Q =>
      change
        some
          (HallMarriageUp.mk
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist L))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist R))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist E))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist N))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist S))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist B))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist A))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist M))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist U))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist P))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist C))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist T))
            (hallMarriageDecodeBHist (hallMarriageEncodeBHist Q))) =
          some (HallMarriageUp.mk L R E N S B A M U P C T Q)
      rw [HallMarriageTasteGate_single_carrier_alignment_decode L,
        HallMarriageTasteGate_single_carrier_alignment_decode R,
        HallMarriageTasteGate_single_carrier_alignment_decode E,
        HallMarriageTasteGate_single_carrier_alignment_decode N,
        HallMarriageTasteGate_single_carrier_alignment_decode S,
        HallMarriageTasteGate_single_carrier_alignment_decode B,
        HallMarriageTasteGate_single_carrier_alignment_decode A,
        HallMarriageTasteGate_single_carrier_alignment_decode M,
        HallMarriageTasteGate_single_carrier_alignment_decode U,
        HallMarriageTasteGate_single_carrier_alignment_decode P,
        HallMarriageTasteGate_single_carrier_alignment_decode C,
        HallMarriageTasteGate_single_carrier_alignment_decode T,
        HallMarriageTasteGate_single_carrier_alignment_decode Q]

private theorem HallMarriageTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HallMarriageUp} :
    hallMarriageToEventFlow x = hallMarriageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hallMarriageFromEventFlow (hallMarriageToEventFlow x) =
        hallMarriageFromEventFlow (hallMarriageToEventFlow y) :=
    congrArg hallMarriageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HallMarriageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HallMarriageTasteGate_single_carrier_alignment_round_trip y)))

private theorem HallMarriageTasteGate_single_carrier_alignment_fields :
    ∀ x y : HallMarriageUp, hallMarriageFields x = hallMarriageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 R1 E1 N1 S1 B1 A1 M1 U1 P1 C1 T1 Q1 =>
      cases y with
      | mk L2 R2 E2 N2 S2 B2 A2 M2 U2 P2 C2 T2 Q2 =>
          cases hfields
          rfl

instance hallMarriageBHistCarrier : BHistCarrier HallMarriageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hallMarriageToEventFlow
  fromEventFlow := hallMarriageFromEventFlow

instance hallMarriageChapterTasteGate : ChapterTasteGate HallMarriageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hallMarriageFromEventFlow (hallMarriageToEventFlow x) = some x
    exact HallMarriageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HallMarriageTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hallMarriageFieldFaithful : FieldFaithful HallMarriageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hallMarriageFields
  field_faithful := HallMarriageTasteGate_single_carrier_alignment_fields

instance hallMarriageNontrivial : Nontrivial HallMarriageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HallMarriageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HallMarriageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HallMarriageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hallMarriageChapterTasteGate

theorem HallMarriageTasteGate_single_carrier_alignment :
    (∀ h : BHist, hallMarriageDecodeBHist (hallMarriageEncodeBHist h) = h) ∧
      (∀ x : HallMarriageUp, hallMarriageFromEventFlow (hallMarriageToEventFlow x) = some x) ∧
        (∀ x y : HallMarriageUp, hallMarriageToEventFlow x = hallMarriageToEventFlow y → x = y) ∧
          hallMarriageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨HallMarriageTasteGate_single_carrier_alignment_decode,
      HallMarriageTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HallMarriageTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HallMarriageUp
