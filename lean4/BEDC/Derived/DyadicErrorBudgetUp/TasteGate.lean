import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicErrorBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicErrorBudgetUp : Type where
  | mk (Q A B S WX WY DX DY DZ RX RY T H C P N : BHist) : DyadicErrorBudgetUp
  deriving DecidableEq

def dyadicErrorBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicErrorBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicErrorBudgetEncodeBHist h

def dyadicErrorBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicErrorBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicErrorBudgetDecodeBHist tail)

theorem DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem DyadicErrorBudgetUpTasteGate_single_carrier_alignment_mk_congr
    {Q Q' A A' B B' S S' WX WX' WY WY' DX DX' DY DY' DZ DZ' RX RX' RY RY'
      T T' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q)
    (hA : A' = A)
    (hB : B' = B)
    (hS : S' = S)
    (hWX : WX' = WX)
    (hWY : WY' = WY)
    (hDX : DX' = DX)
    (hDY : DY' = DY)
    (hDZ : DZ' = DZ)
    (hRX : RX' = RX)
    (hRY : RY' = RY)
    (hT : T' = T)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    DyadicErrorBudgetUp.mk Q' A' B' S' WX' WY' DX' DY' DZ' RX' RY' T' H' C' P' N' =
      DyadicErrorBudgetUp.mk Q A B S WX WY DX DY DZ RX RY T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hA
  cases hB
  cases hS
  cases hWX
  cases hWY
  cases hDX
  cases hDY
  cases hDZ
  cases hRX
  cases hRY
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def dyadicErrorBudgetToEventFlow : DyadicErrorBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicErrorBudgetUp.mk Q A B S WX WY DX DY DZ RX RY T H C P N =>
      [dyadicErrorBudgetEncodeBHist Q,
        dyadicErrorBudgetEncodeBHist A,
        dyadicErrorBudgetEncodeBHist B,
        dyadicErrorBudgetEncodeBHist S,
        dyadicErrorBudgetEncodeBHist WX,
        dyadicErrorBudgetEncodeBHist WY,
        dyadicErrorBudgetEncodeBHist DX,
        dyadicErrorBudgetEncodeBHist DY,
        dyadicErrorBudgetEncodeBHist DZ,
        dyadicErrorBudgetEncodeBHist RX,
        dyadicErrorBudgetEncodeBHist RY,
        dyadicErrorBudgetEncodeBHist T,
        dyadicErrorBudgetEncodeBHist H,
        dyadicErrorBudgetEncodeBHist C,
        dyadicErrorBudgetEncodeBHist P,
        dyadicErrorBudgetEncodeBHist N]

def dyadicErrorBudgetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicErrorBudgetEventAt index rest

def dyadicErrorBudgetFromEventFlow (ef : EventFlow) : Option DyadicErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicErrorBudgetUp.mk
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 0 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 1 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 2 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 3 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 4 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 5 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 6 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 7 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 8 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 9 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 10 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 11 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 12 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 13 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 14 ef))
      (dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEventAt 15 ef)))

theorem DyadicErrorBudgetUpTasteGate_single_carrier_alignment_round_trip
    : ∀ x : DyadicErrorBudgetUp,
    dyadicErrorBudgetFromEventFlow (dyadicErrorBudgetToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicErrorBudgetUp.mk Q A B S WX WY DX DY DZ RX RY T H C P N =>
      congrArg some
        (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_mk_congr
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode Q)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode A)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode B)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode S)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode WX)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode WY)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode DX)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode DY)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode DZ)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode RX)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode RY)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode T)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode H)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode C)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode P)
          (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode N))

theorem DyadicErrorBudgetUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicErrorBudgetUp} :
    dyadicErrorBudgetToEventFlow x = dyadicErrorBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicErrorBudgetFromEventFlow (dyadicErrorBudgetToEventFlow x) =
        dyadicErrorBudgetFromEventFlow (dyadicErrorBudgetToEventFlow y) :=
    congrArg dyadicErrorBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicErrorBudgetBHistCarrier : BHistCarrier DyadicErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicErrorBudgetToEventFlow
  fromEventFlow := dyadicErrorBudgetFromEventFlow

instance dyadicErrorBudgetChapterTasteGate : ChapterTasteGate DyadicErrorBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicErrorBudgetFromEventFlow (dyadicErrorBudgetToEventFlow x) = some x
    exact DyadicErrorBudgetUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicErrorBudgetUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicErrorBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicErrorBudgetChapterTasteGate

theorem DyadicErrorBudgetUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicErrorBudgetDecodeBHist (dyadicErrorBudgetEncodeBHist h) = h) ∧
      (∀ x : DyadicErrorBudgetUp,
        dyadicErrorBudgetFromEventFlow (dyadicErrorBudgetToEventFlow x) = some x) ∧
      (∀ x y : DyadicErrorBudgetUp,
        dyadicErrorBudgetToEventFlow x = dyadicErrorBudgetToEventFlow y → x = y) ∧
      dyadicErrorBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicErrorBudgetUpTasteGate_single_carrier_alignment_decode_encode,
      DyadicErrorBudgetUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicErrorBudgetUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicErrorBudgetUp
