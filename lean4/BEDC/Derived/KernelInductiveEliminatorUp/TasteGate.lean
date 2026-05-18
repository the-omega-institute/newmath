import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelInductiveEliminatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelInductiveEliminatorUp : Type where
  | mk (D S L M R B H C P N : BHist) : KernelInductiveEliminatorUp
  deriving DecidableEq

def kernelInductiveEliminatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelInductiveEliminatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelInductiveEliminatorEncodeBHist h

def kernelInductiveEliminatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelInductiveEliminatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelInductiveEliminatorDecodeBHist tail)

private theorem KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelInductiveEliminator_mk_congr
    {D D' S S' L L' M M' R R' B B' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hS : S' = S) (hL : L' = L) (hM : M' = M)
    (hR : R' = R) (hB : B' = B) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    KernelInductiveEliminatorUp.mk D' S' L' M' R' B' H' C' P' N' =
      KernelInductiveEliminatorUp.mk D S L M R B H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hS
  cases hL
  cases hM
  cases hR
  cases hB
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def kernelInductiveEliminatorFields : KernelInductiveEliminatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KernelInductiveEliminatorUp.mk D S L M R B H C P N => [D, S, L, M, R, B, H, C, P, N]

def kernelInductiveEliminatorToEventFlow : KernelInductiveEliminatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kernelInductiveEliminatorFields x).map kernelInductiveEliminatorEncodeBHist

private def kernelInductiveEliminatorRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => kernelInductiveEliminatorRawAt n rest

private def kernelInductiveEliminatorLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => kernelInductiveEliminatorLengthEq n rest

def kernelInductiveEliminatorFromEventFlow : EventFlow → Option KernelInductiveEliminatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match kernelInductiveEliminatorLengthEq 10 flow with
      | true =>
          some
            (KernelInductiveEliminatorUp.mk
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 0 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 1 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 2 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 3 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 4 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 5 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 6 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 7 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 8 flow))
              (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorRawAt 9 flow)))
      | false => none

private theorem KernelInductiveEliminatorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KernelInductiveEliminatorUp,
      kernelInductiveEliminatorFromEventFlow (kernelInductiveEliminatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S L M R B H C P N =>
      change
        some
          (KernelInductiveEliminatorUp.mk
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist D))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist S))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist L))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist M))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist R))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist B))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist H))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist C))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist P))
            (kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist N))) =
          some (KernelInductiveEliminatorUp.mk D S L M R B H C P N)
      exact
        congrArg some
          (kernelInductiveEliminator_mk_congr
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode D)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode S)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode L)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode M)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode R)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode B)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode H)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode C)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode P)
            (KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode N))

private theorem KernelInductiveEliminatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KernelInductiveEliminatorUp} :
    kernelInductiveEliminatorToEventFlow x = kernelInductiveEliminatorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelInductiveEliminatorFromEventFlow (kernelInductiveEliminatorToEventFlow x) =
        kernelInductiveEliminatorFromEventFlow (kernelInductiveEliminatorToEventFlow y) :=
    congrArg kernelInductiveEliminatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KernelInductiveEliminatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KernelInductiveEliminatorTasteGate_single_carrier_alignment_round_trip y)))

private theorem KernelInductiveEliminatorTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : KernelInductiveEliminatorUp,
      kernelInductiveEliminatorFields x = kernelInductiveEliminatorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ L₁ M₁ R₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ L₂ M₂ R₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance kernelInductiveEliminatorBHistCarrier :
    BHistCarrier KernelInductiveEliminatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelInductiveEliminatorToEventFlow
  fromEventFlow := kernelInductiveEliminatorFromEventFlow

instance kernelInductiveEliminatorChapterTasteGate :
    ChapterTasteGate KernelInductiveEliminatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelInductiveEliminatorFromEventFlow (kernelInductiveEliminatorToEventFlow x) = some x
    exact KernelInductiveEliminatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KernelInductiveEliminatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kernelInductiveEliminatorFieldFaithful :
    FieldFaithful KernelInductiveEliminatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kernelInductiveEliminatorFields
  field_faithful := KernelInductiveEliminatorTasteGate_single_carrier_alignment_fields_faithful

instance kernelInductiveEliminatorNontrivial :
    Nontrivial KernelInductiveEliminatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KernelInductiveEliminatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KernelInductiveEliminatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KernelInductiveEliminatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelInductiveEliminatorChapterTasteGate

namespace TasteGate

theorem KernelInductiveEliminatorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelInductiveEliminatorDecodeBHist (kernelInductiveEliminatorEncodeBHist h) = h) ∧
      (∀ x : KernelInductiveEliminatorUp,
        kernelInductiveEliminatorFromEventFlow (kernelInductiveEliminatorToEventFlow x) =
          some x) ∧
        (∀ x y : KernelInductiveEliminatorUp,
          kernelInductiveEliminatorToEventFlow x = kernelInductiveEliminatorToEventFlow y →
            x = y) ∧
          kernelInductiveEliminatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨KernelInductiveEliminatorTasteGate_single_carrier_alignment_decode_encode,
      KernelInductiveEliminatorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KernelInductiveEliminatorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.KernelInductiveEliminatorUp
