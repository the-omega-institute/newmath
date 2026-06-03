import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDyadicExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDyadicExpansionUp : Type where
  | mk (S W E T F A R L H C P N : BHist) : SignedDyadicExpansionUp
  deriving DecidableEq

def signedDyadicExpansionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDyadicExpansionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDyadicExpansionEncodeBHist h

def signedDyadicExpansionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDyadicExpansionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDyadicExpansionDecodeBHist tail)

private theorem signedDyadicExpansionDecode_encode :
    ∀ h : BHist, signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def signedDyadicExpansionFields : SignedDyadicExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDyadicExpansionUp.mk S W E T F A R L H C P N =>
      [S, W, E, T, F, A, R, L, H, C, P, N]

def signedDyadicExpansionToEventFlow : SignedDyadicExpansionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (signedDyadicExpansionFields x).map signedDyadicExpansionEncodeBHist

private def signedDyadicExpansionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => signedDyadicExpansionEventAt index rest

def signedDyadicExpansionFromEventFlow (ef : EventFlow) : Option SignedDyadicExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SignedDyadicExpansionUp.mk
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 0 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 1 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 2 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 3 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 4 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 5 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 6 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 7 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 8 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 9 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 10 ef))
      (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEventAt 11 ef)))

private theorem signedDyadicExpansion_round_trip (x : SignedDyadicExpansionUp) :
    signedDyadicExpansionFromEventFlow (signedDyadicExpansionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W E T F A R L H C P N =>
      change
        some
          (SignedDyadicExpansionUp.mk
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist S))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist W))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist E))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist T))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist F))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist A))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist R))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist L))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist H))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist C))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist P))
            (signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist N))) =
          some (SignedDyadicExpansionUp.mk S W E T F A R L H C P N)
      rw [signedDyadicExpansionDecode_encode S, signedDyadicExpansionDecode_encode W,
        signedDyadicExpansionDecode_encode E, signedDyadicExpansionDecode_encode T,
        signedDyadicExpansionDecode_encode F, signedDyadicExpansionDecode_encode A,
        signedDyadicExpansionDecode_encode R, signedDyadicExpansionDecode_encode L,
        signedDyadicExpansionDecode_encode H, signedDyadicExpansionDecode_encode C,
        signedDyadicExpansionDecode_encode P, signedDyadicExpansionDecode_encode N]

private theorem signedDyadicExpansionToEventFlow_injective
    {x y : SignedDyadicExpansionUp} :
    signedDyadicExpansionToEventFlow x = signedDyadicExpansionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDyadicExpansionFromEventFlow (signedDyadicExpansionToEventFlow x) =
        signedDyadicExpansionFromEventFlow (signedDyadicExpansionToEventFlow y) :=
    congrArg signedDyadicExpansionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (signedDyadicExpansion_round_trip x).symm
      (Eq.trans hread (signedDyadicExpansion_round_trip y)))

instance signedDyadicExpansionBHistCarrier :
    BHistCarrier SignedDyadicExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDyadicExpansionToEventFlow
  fromEventFlow := signedDyadicExpansionFromEventFlow

instance signedDyadicExpansionChapterTasteGate :
    ChapterTasteGate SignedDyadicExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change signedDyadicExpansionFromEventFlow (signedDyadicExpansionToEventFlow x) = some x
    exact signedDyadicExpansion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (signedDyadicExpansionToEventFlow_injective heq)

theorem SignedDyadicExpansionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      signedDyadicExpansionDecodeBHist (signedDyadicExpansionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SignedDyadicExpansionUp) ∧
        Nonempty (ChapterTasteGate SignedDyadicExpansionUp) ∧
          signedDyadicExpansionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact signedDyadicExpansionDecode_encode
  · constructor
    · exact ⟨signedDyadicExpansionBHistCarrier⟩
    · constructor
      · exact ⟨signedDyadicExpansionChapterTasteGate⟩
      · rfl

end BEDC.Derived.SignedDyadicExpansionUp
