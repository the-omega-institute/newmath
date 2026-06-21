import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MobiusTransformUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MobiusTransformUp : Type where
  | mk (A B C D G PJ HD XR H K Q N : BHist) : MobiusTransformUp
  deriving DecidableEq

def mobiusTransformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mobiusTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mobiusTransformEncodeBHist h

def mobiusTransformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mobiusTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mobiusTransformDecodeBHist tail)

private theorem MobiusTransformTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, mobiusTransformDecodeBHist (mobiusTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mobiusTransformFields : MobiusTransformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MobiusTransformUp.mk A B C D G PJ HD XR H K Q N => [A, B, C, D, G, PJ, HD, XR, H, K, Q, N]

def mobiusTransformToEventFlow : MobiusTransformUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (mobiusTransformFields x).map mobiusTransformEncodeBHist

private def mobiusTransformEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mobiusTransformEventAtDefault index rest

def mobiusTransformFromEventFlow (ef : EventFlow) : Option MobiusTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MobiusTransformUp.mk
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 0 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 1 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 2 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 3 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 4 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 5 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 6 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 7 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 8 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 9 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 10 ef))
      (mobiusTransformDecodeBHist (mobiusTransformEventAtDefault 11 ef)))

private theorem MobiusTransformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MobiusTransformUp, mobiusTransformFromEventFlow (mobiusTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B C D G PJ HD XR H K Q N =>
      change
        some
          (MobiusTransformUp.mk
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist A))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist B))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist C))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist D))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist G))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist PJ))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist HD))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist XR))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist H))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist K))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist Q))
            (mobiusTransformDecodeBHist (mobiusTransformEncodeBHist N))) =
          some (MobiusTransformUp.mk A B C D G PJ HD XR H K Q N)
      rw [MobiusTransformTasteGate_single_carrier_alignment_decode A,
        MobiusTransformTasteGate_single_carrier_alignment_decode B,
        MobiusTransformTasteGate_single_carrier_alignment_decode C,
        MobiusTransformTasteGate_single_carrier_alignment_decode D,
        MobiusTransformTasteGate_single_carrier_alignment_decode G,
        MobiusTransformTasteGate_single_carrier_alignment_decode PJ,
        MobiusTransformTasteGate_single_carrier_alignment_decode HD,
        MobiusTransformTasteGate_single_carrier_alignment_decode XR,
        MobiusTransformTasteGate_single_carrier_alignment_decode H,
        MobiusTransformTasteGate_single_carrier_alignment_decode K,
        MobiusTransformTasteGate_single_carrier_alignment_decode Q,
        MobiusTransformTasteGate_single_carrier_alignment_decode N]

private theorem MobiusTransformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MobiusTransformUp} :
    mobiusTransformToEventFlow x = mobiusTransformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mobiusTransformFromEventFlow (mobiusTransformToEventFlow x) =
        mobiusTransformFromEventFlow (mobiusTransformToEventFlow y) :=
    congrArg mobiusTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MobiusTransformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MobiusTransformTasteGate_single_carrier_alignment_round_trip y)))

instance mobiusTransformBHistCarrier : BHistCarrier MobiusTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mobiusTransformToEventFlow
  fromEventFlow := mobiusTransformFromEventFlow

instance mobiusTransformChapterTasteGate : ChapterTasteGate MobiusTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mobiusTransformFromEventFlow (mobiusTransformToEventFlow x) = some x
    exact MobiusTransformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MobiusTransformTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance mobiusTransformNontrivial : Nontrivial MobiusTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MobiusTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MobiusTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MobiusTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mobiusTransformChapterTasteGate

theorem MobiusTransformTasteGate_single_carrier_alignment :
    (∀ h : BHist, mobiusTransformDecodeBHist (mobiusTransformEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MobiusTransformUp) ∧ Nonempty (ChapterTasteGate MobiusTransformUp) ∧
        mobiusTransformEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MobiusTransformTasteGate_single_carrier_alignment_decode,
      ⟨mobiusTransformBHistCarrier⟩, ⟨mobiusTransformChapterTasteGate⟩, rfl⟩

end BEDC.Derived.MobiusTransformUp.TasteGate
