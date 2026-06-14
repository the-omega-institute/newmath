import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterSpaceUp : Type where
  | mk (X B W Q S R E H C P N : BHist) : RegularCauchyFilterSpaceUp
  deriving DecidableEq

def regularCauchyFilterSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterSpaceEncodeBHist h

def regularCauchyFilterSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterSpaceDecodeBHist tail)

private theorem RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyFilterSpaceDecodeBHist (regularCauchyFilterSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_mk_congr
    {X X' B B' W W' Q Q' S S' R R' E E' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hB : B' = B) (hW : W' = W) (hQ : Q' = Q)
    (hS : S' = S) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyFilterSpaceUp.mk X' B' W' Q' S' R' E' H' C' P' N' =
      RegularCauchyFilterSpaceUp.mk X B W Q S R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hB
  cases hW
  cases hQ
  cases hS
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyFilterSpaceFields :
    RegularCauchyFilterSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterSpaceUp.mk X B W Q S R E H C P N =>
      [X, B, W, Q, S, R, E, H, C, P, N]

def regularCauchyFilterSpaceToEventFlow :
    RegularCauchyFilterSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyFilterSpaceFields x).map regularCauchyFilterSpaceEncodeBHist

private def RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest =>
      RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt n rest

private def RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest =>
      RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_lengthEq n rest

def regularCauchyFilterSpaceFromEventFlow :
    EventFlow → Option RegularCauchyFilterSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_lengthEq 11 flow with
      | true =>
          some
            (RegularCauchyFilterSpaceUp.mk
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 0 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 1 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 2 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 3 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 4 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 5 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 6 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 7 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 8 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 9 flow))
              (regularCauchyFilterSpaceDecodeBHist
                (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_rawAt 10 flow)))
      | false => none

private theorem RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyFilterSpaceUp,
      regularCauchyFilterSpaceFromEventFlow
        (regularCauchyFilterSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B W Q S R E H C P N =>
      exact
        congrArg some
          (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_mk_congr
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode X)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode B)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode W)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode Q)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode S)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode R)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode E)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode H)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode C)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode P)
            (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode N))

private theorem RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFilterSpaceUp} :
    regularCauchyFilterSpaceToEventFlow x =
      regularCauchyFilterSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterSpaceFromEventFlow (regularCauchyFilterSpaceToEventFlow x) =
        regularCauchyFilterSpaceFromEventFlow (regularCauchyFilterSpaceToEventFlow y) :=
    congrArg regularCauchyFilterSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyFilterSpaceBHistCarrier :
    BHistCarrier RegularCauchyFilterSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterSpaceToEventFlow
  fromEventFlow := regularCauchyFilterSpaceFromEventFlow

instance regularCauchyFilterSpaceChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFilterSpaceFromEventFlow (regularCauchyFilterSpaceToEventFlow x) = some x
    exact RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyFilterSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyFilterSpaceDecodeBHist (regularCauchyFilterSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyFilterSpaceUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyFilterSpaceUp) ∧
          regularCauchyFilterSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyFilterSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyFilterSpaceBHistCarrier⟩,
      ⟨regularCauchyFilterSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyFilterSpaceUp
