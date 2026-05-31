import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSimplicialChainUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSimplicialChainUp : Type where
  | mk (K F A G B Z H T P N : BHist) : FiniteSimplicialChainUp
  deriving DecidableEq

def finiteSimplicialChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSimplicialChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSimplicialChainEncodeBHist h

def finiteSimplicialChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSimplicialChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSimplicialChainDecodeBHist tail)

private theorem FiniteSimplicialChainTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSimplicialChainFields : FiniteSimplicialChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSimplicialChainUp.mk K F A G B Z H T P N => [K, F, A, G, B, Z, H, T, P, N]

def finiteSimplicialChainToEventFlow : FiniteSimplicialChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSimplicialChainFields x).map finiteSimplicialChainEncodeBHist

def finiteSimplicialChainFromEventFlow : EventFlow → Option FiniteSimplicialChainUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _K :: [] => none
  | _K :: _F :: [] => none
  | _K :: _F :: _A :: [] => none
  | _K :: _F :: _A :: _G :: [] => none
  | _K :: _F :: _A :: _G :: _B :: [] => none
  | _K :: _F :: _A :: _G :: _B :: _Z :: [] => none
  | _K :: _F :: _A :: _G :: _B :: _Z :: _H :: [] => none
  | _K :: _F :: _A :: _G :: _B :: _Z :: _H :: _T :: [] => none
  | _K :: _F :: _A :: _G :: _B :: _Z :: _H :: _T :: _P :: [] => none
  | K :: F :: A :: G :: B :: Z :: H :: T :: P :: N :: [] =>
      some
        (FiniteSimplicialChainUp.mk
          (finiteSimplicialChainDecodeBHist K)
          (finiteSimplicialChainDecodeBHist F)
          (finiteSimplicialChainDecodeBHist A)
          (finiteSimplicialChainDecodeBHist G)
          (finiteSimplicialChainDecodeBHist B)
          (finiteSimplicialChainDecodeBHist Z)
          (finiteSimplicialChainDecodeBHist H)
          (finiteSimplicialChainDecodeBHist T)
          (finiteSimplicialChainDecodeBHist P)
          (finiteSimplicialChainDecodeBHist N))
  | _K :: _F :: _A :: _G :: _B :: _Z :: _H :: _T :: _P :: _N :: _extra :: _rest =>
      none

private theorem FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteSimplicialChainUp,
      finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F A G B Z H T P N =>
      change
        some
          (FiniteSimplicialChainUp.mk
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist K))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist F))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist A))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist G))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist B))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist Z))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist H))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist T))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist P))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist N))) =
          some (FiniteSimplicialChainUp.mk K F A G B Z H T P N)
      rw [FiniteSimplicialChainTasteGate_single_carrier_alignment_decode K,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode F,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode A,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode G,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode B,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode Z,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode H,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode T,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode P,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode N]

private theorem FiniteSimplicialChainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSimplicialChainUp} :
    finiteSimplicialChainToEventFlow x = finiteSimplicialChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) =
        finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow y) :=
    congrArg finiteSimplicialChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip y)))

instance finiteSimplicialChainBHistCarrier : BHistCarrier FiniteSimplicialChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSimplicialChainToEventFlow
  fromEventFlow := finiteSimplicialChainFromEventFlow

instance finiteSimplicialChainChapterTasteGate : ChapterTasteGate FiniteSimplicialChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x
    exact FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSimplicialChainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteSimplicialChainTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteSimplicialChainUp) ∧
      (∀ h : BHist, finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist h) = h) ∧
      (∀ x : FiniteSimplicialChainUp,
        finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x) ∧
      (∀ x y : FiniteSimplicialChainUp,
        finiteSimplicialChainToEventFlow x = finiteSimplicialChainToEventFlow y → x = y) ∧
      finiteSimplicialChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨finiteSimplicialChainChapterTasteGate⟩
  constructor
  · exact FiniteSimplicialChainTasteGate_single_carrier_alignment_decode
  constructor
  · exact FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y
    exact FiniteSimplicialChainTasteGate_single_carrier_alignment_toEventFlow_injective
  · rfl

end BEDC.Derived.FiniteSimplicialChainUp.TasteGate
