import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCauchyModulusLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCauchyModulusLatticeUp : Type where
  | mk (D M W Q R J H C P N : BHist) : DyadicCauchyModulusLatticeUp
  deriving DecidableEq

def dyadicCauchyModulusLatticeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCauchyModulusLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCauchyModulusLatticeEncodeBHist h

def dyadicCauchyModulusLatticeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCauchyModulusLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCauchyModulusLatticeDecodeBHist tail)

private theorem DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      dyadicCauchyModulusLatticeDecodeBHist
          (dyadicCauchyModulusLatticeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCauchyModulusLatticeFields : DyadicCauchyModulusLatticeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCauchyModulusLatticeUp.mk D M W Q R J H C P N => [D, M, W, Q, R, J, H, C, P, N]

def dyadicCauchyModulusLatticeToEventFlow :
    DyadicCauchyModulusLatticeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCauchyModulusLatticeFields x).map dyadicCauchyModulusLatticeEncodeBHist

private def dyadicCauchyModulusLatticeEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicCauchyModulusLatticeEventAt index rest

def dyadicCauchyModulusLatticeFromEventFlow
    (flow : EventFlow) : Option DyadicCauchyModulusLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCauchyModulusLatticeUp.mk
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 0 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 1 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 2 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 3 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 4 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 5 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 6 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 7 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 8 flow))
      (dyadicCauchyModulusLatticeDecodeBHist (dyadicCauchyModulusLatticeEventAt 9 flow)))

private theorem DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicCauchyModulusLatticeUp,
      dyadicCauchyModulusLatticeFromEventFlow
          (dyadicCauchyModulusLatticeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M W Q R J H C P N =>
      change
        some
          (DyadicCauchyModulusLatticeUp.mk
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist D))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist M))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist W))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist Q))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist R))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist J))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist H))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist C))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist P))
            (dyadicCauchyModulusLatticeDecodeBHist
              (dyadicCauchyModulusLatticeEncodeBHist N))) =
          some (DyadicCauchyModulusLatticeUp.mk D M W Q R J H C P N)
      rw [DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode D,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode M,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode W,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode R,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode J,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode H,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode C,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode P,
        DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCauchyModulusLatticeUp} :
    dyadicCauchyModulusLatticeToEventFlow x =
      dyadicCauchyModulusLatticeToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCauchyModulusLatticeFromEventFlow
          (dyadicCauchyModulusLatticeToEventFlow x) =
        dyadicCauchyModulusLatticeFromEventFlow
          (dyadicCauchyModulusLatticeToEventFlow y) :=
    congrArg dyadicCauchyModulusLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicCauchyModulusLatticeBHistCarrier :
    BHistCarrier DyadicCauchyModulusLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCauchyModulusLatticeToEventFlow
  fromEventFlow := dyadicCauchyModulusLatticeFromEventFlow

instance dyadicCauchyModulusLatticeChapterTasteGate :
    ChapterTasteGate DyadicCauchyModulusLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicCauchyModulusLatticeFromEventFlow
          (dyadicCauchyModulusLatticeToEventFlow x) =
        some x
    exact DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicCauchyModulusLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCauchyModulusLatticeChapterTasteGate

theorem DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dyadicCauchyModulusLatticeDecodeBHist
          (dyadicCauchyModulusLatticeEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier DyadicCauchyModulusLatticeUp) ∧
        Nonempty (ChapterTasteGate DyadicCauchyModulusLatticeUp) ∧
          dyadicCauchyModulusLatticeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact DyadicCauchyModulusLatticeTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨dyadicCauchyModulusLatticeBHistCarrier⟩
    · constructor
      · exact ⟨dyadicCauchyModulusLatticeChapterTasteGate⟩
      · rfl

end BEDC.Derived.DyadicCauchyModulusLatticeUp
