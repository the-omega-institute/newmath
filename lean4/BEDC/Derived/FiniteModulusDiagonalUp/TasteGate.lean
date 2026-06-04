import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteModulusDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteModulusDiagonalUp : Type where
  | mk : (M S T Q E H C P N : BHist) -> FiniteModulusDiagonalUp
  deriving DecidableEq

def finiteModulusDiagonalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteModulusDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteModulusDiagonalEncodeBHist h

def finiteModulusDiagonalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteModulusDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteModulusDiagonalDecodeBHist tail)

private theorem finiteModulusDiagonalDecodeEncode :
    forall h : BHist, finiteModulusDiagonalDecodeBHist
        (finiteModulusDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteModulusDiagonalFields : FiniteModulusDiagonalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteModulusDiagonalUp.mk M S T Q E H C P N => [M, S, T, Q, E, H, C, P, N]

def finiteModulusDiagonalToEventFlow : FiniteModulusDiagonalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteModulusDiagonalFields x).map finiteModulusDiagonalEncodeBHist

def finiteModulusDiagonalFromEventFlow : EventFlow -> Option FiniteModulusDiagonalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [M, S, T, Q, E, H, C, P, N] =>
      some
        (FiniteModulusDiagonalUp.mk
          (finiteModulusDiagonalDecodeBHist M)
          (finiteModulusDiagonalDecodeBHist S)
          (finiteModulusDiagonalDecodeBHist T)
          (finiteModulusDiagonalDecodeBHist Q)
          (finiteModulusDiagonalDecodeBHist E)
          (finiteModulusDiagonalDecodeBHist H)
          (finiteModulusDiagonalDecodeBHist C)
          (finiteModulusDiagonalDecodeBHist P)
          (finiteModulusDiagonalDecodeBHist N))
  | _ => none

private theorem finiteModulusDiagonalRoundTrip (x : FiniteModulusDiagonalUp) :
    finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S T Q E H C P N =>
      change
        some
          (FiniteModulusDiagonalUp.mk
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist M))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist S))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist T))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist Q))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist E))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist H))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist C))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist P))
            (finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist N))) =
          some (FiniteModulusDiagonalUp.mk M S T Q E H C P N)
      rw [finiteModulusDiagonalDecodeEncode M, finiteModulusDiagonalDecodeEncode S,
        finiteModulusDiagonalDecodeEncode T, finiteModulusDiagonalDecodeEncode Q,
        finiteModulusDiagonalDecodeEncode E, finiteModulusDiagonalDecodeEncode H,
        finiteModulusDiagonalDecodeEncode C, finiteModulusDiagonalDecodeEncode P,
        finiteModulusDiagonalDecodeEncode N]

private theorem finiteModulusDiagonalToEventFlow_injective {x y : FiniteModulusDiagonalUp} :
    finiteModulusDiagonalToEventFlow x = finiteModulusDiagonalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow x) =
        finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow y) :=
    congrArg finiteModulusDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteModulusDiagonalRoundTrip x).symm
      (Eq.trans hread (finiteModulusDiagonalRoundTrip y)))

private theorem finiteModulusDiagonalFieldsFaithful (x y : FiniteModulusDiagonalUp) :
    finiteModulusDiagonalFields x = finiteModulusDiagonalFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk M1 S1 T1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 S2 T2 Q2 E2 H2 C2 P2 N2 =>
          injection h with hM tail0
          injection tail0 with hS tail1
          injection tail1 with hT tail2
          injection tail2 with hQ tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hM
          subst hS
          subst hT
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance finiteModulusDiagonalBHistCarrier : BHistCarrier FiniteModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteModulusDiagonalToEventFlow
  fromEventFlow := finiteModulusDiagonalFromEventFlow

instance finiteModulusDiagonalChapterTasteGate : ChapterTasteGate FiniteModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow x) = some x
    exact finiteModulusDiagonalRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteModulusDiagonalToEventFlow_injective heq)

instance finiteModulusDiagonalFieldFaithful : FieldFaithful FiniteModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteModulusDiagonalFields
  field_faithful := finiteModulusDiagonalFieldsFaithful

instance finiteModulusDiagonalNontrivial : Nontrivial FiniteModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteModulusDiagonalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteModulusDiagonalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteModulusDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteModulusDiagonalChapterTasteGate

theorem FiniteModulusDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteModulusDiagonalDecodeBHist
      (finiteModulusDiagonalEncodeBHist h) = h) ∧
      (∀ M S T Q E H C P N : BHist,
        finiteModulusDiagonalFields (FiniteModulusDiagonalUp.mk M S T Q E H C P N) =
          [M, S, T, Q, E, H, C, P, N]) ∧
        (∀ x y : FiniteModulusDiagonalUp,
          finiteModulusDiagonalFields x = finiteModulusDiagonalFields y -> x = y) ∧
          Not
            (FiniteModulusDiagonalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty =
              FiniteModulusDiagonalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ∧
            finiteModulusDiagonalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact finiteModulusDiagonalDecodeEncode
  · constructor
    · intro M S T Q E H C P N
      rfl
    · constructor
      · exact finiteModulusDiagonalFieldsFaithful
      · constructor
        · intro h
          cases h
        · rfl

end BEDC.Derived.FiniteModulusDiagonalUp
