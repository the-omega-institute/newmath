import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegSeqRatLocatedModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegSeqRatLocatedModulusUp : Type where
  | mk (Q L mu W D R E H C P N : BHist) : RegSeqRatLocatedModulusUp
  deriving DecidableEq

def regSeqRatLocatedModulusEncodeBHist : BHist -> List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regSeqRatLocatedModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regSeqRatLocatedModulusEncodeBHist h

def regSeqRatLocatedModulusDecodeBHist : List BMark -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regSeqRatLocatedModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regSeqRatLocatedModulusDecodeBHist tail)

private theorem RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regSeqRatLocatedModulusFields : RegSeqRatLocatedModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegSeqRatLocatedModulusUp.mk Q L mu W D R E H C P N =>
      [Q, L, mu, W, D, R, E, H, C, P, N]

def regSeqRatLocatedModulusToEventFlow : RegSeqRatLocatedModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regSeqRatLocatedModulusEncodeBHist (regSeqRatLocatedModulusFields x)

private def regSeqRatLocatedModulusEventAt : Nat -> EventFlow -> List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regSeqRatLocatedModulusEventAt index rest

def regSeqRatLocatedModulusFromEventFlow (ef : EventFlow) :
    Option RegSeqRatLocatedModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegSeqRatLocatedModulusUp.mk
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 0 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 1 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 2 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 3 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 4 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 5 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 6 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 7 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 8 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 9 ef))
      (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEventAt 10 ef)))

private theorem RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_round_trip
    (x : RegSeqRatLocatedModulusUp) :
    regSeqRatLocatedModulusFromEventFlow (regSeqRatLocatedModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q L mu W D R E H C P N =>
      change
        some
          (RegSeqRatLocatedModulusUp.mk
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist Q))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist L))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist mu))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist W))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist D))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist R))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist E))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist H))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist C))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist P))
            (regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist N))) =
          some (RegSeqRatLocatedModulusUp.mk Q L mu W D R E H C P N)
      rw [RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode Q,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode L,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode mu,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode W,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode D,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode R,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode E,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode H,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode C,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode P,
        RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode N]

private theorem RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegSeqRatLocatedModulusUp} :
    regSeqRatLocatedModulusToEventFlow x = regSeqRatLocatedModulusToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regSeqRatLocatedModulusFromEventFlow (regSeqRatLocatedModulusToEventFlow x) =
        regSeqRatLocatedModulusFromEventFlow (regSeqRatLocatedModulusToEventFlow y) :=
    congrArg regSeqRatLocatedModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_round_trip y)))

instance regSeqRatLocatedModulusBHistCarrier :
    BHistCarrier RegSeqRatLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regSeqRatLocatedModulusToEventFlow
  fromEventFlow := regSeqRatLocatedModulusFromEventFlow

instance regSeqRatLocatedModulusChapterTasteGate :
    ChapterTasteGate RegSeqRatLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regSeqRatLocatedModulusFromEventFlow
      (regSeqRatLocatedModulusToEventFlow x) = some x
    exact RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegSeqRatLocatedModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regSeqRatLocatedModulusChapterTasteGate

theorem RegSeqRatLocatedModulusTasteGate_single_carrier_alignment :
    (∃ encode : BHist -> List BMark, encode = regSeqRatLocatedModulusEncodeBHist) ∧
      (∀ h : BHist,
        regSeqRatLocatedModulusDecodeBHist (regSeqRatLocatedModulusEncodeBHist h) = h) ∧
        Nonempty RegSeqRatLocatedModulusUp ∧
          Nonempty (BHistCarrier RegSeqRatLocatedModulusUp) ∧
            Nonempty (ChapterTasteGate RegSeqRatLocatedModulusUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨regSeqRatLocatedModulusEncodeBHist, rfl⟩,
      RegSeqRatLocatedModulusTasteGate_single_carrier_alignment_decode,
      ⟨RegSeqRatLocatedModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty⟩,
      ⟨regSeqRatLocatedModulusBHistCarrier⟩,
      ⟨regSeqRatLocatedModulusChapterTasteGate⟩⟩

end BEDC.Derived.RegSeqRatLocatedModulusUp.TasteGate
