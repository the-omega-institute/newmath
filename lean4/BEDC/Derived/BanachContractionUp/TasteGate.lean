import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachContractionUp : Type where
  | mk (K I M Q S E H C P N : BHist) : BanachContractionUp
  deriving DecidableEq

def banachContractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachContractionEncodeBHist h

def banachContractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachContractionDecodeBHist tail)

private theorem BanachContractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, banachContractionDecodeBHist (banachContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem BanachContractionTasteGate_single_carrier_alignment_mk_congr
    {K K' I I' M M' Q Q' S S' E E' H H' C C' P P' N N' : BHist}
    (hK : K' = K)
    (hI : I' = I)
    (hM : M' = M)
    (hQ : Q' = Q)
    (hS : S' = S)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    BanachContractionUp.mk K' I' M' Q' S' E' H' C' P' N' =
      BanachContractionUp.mk K I M Q S E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hI
  cases hM
  cases hQ
  cases hS
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def banachContractionToEventFlow : BanachContractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BanachContractionUp.mk K I M Q S E H C P N =>
      [banachContractionEncodeBHist K,
        banachContractionEncodeBHist I,
        banachContractionEncodeBHist M,
        banachContractionEncodeBHist Q,
        banachContractionEncodeBHist S,
        banachContractionEncodeBHist E,
        banachContractionEncodeBHist H,
        banachContractionEncodeBHist C,
        banachContractionEncodeBHist P,
        banachContractionEncodeBHist N]

private def banachContractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachContractionEventAtDefault index rest

def banachContractionFromEventFlow (ef : EventFlow) : Option BanachContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachContractionUp.mk
      (banachContractionDecodeBHist (banachContractionEventAtDefault 0 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 1 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 2 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 3 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 4 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 5 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 6 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 7 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 8 ef))
      (banachContractionDecodeBHist (banachContractionEventAtDefault 9 ef)))

private theorem BanachContractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachContractionUp,
      banachContractionFromEventFlow (banachContractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K I M Q S E H C P N =>
      exact
        congrArg some
          (BanachContractionTasteGate_single_carrier_alignment_mk_congr
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode K)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode I)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode M)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode Q)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode S)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode E)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode H)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode C)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode P)
            (BanachContractionTasteGate_single_carrier_alignment_decode_encode N))

private theorem BanachContractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachContractionUp} :
    banachContractionToEventFlow x = banachContractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachContractionFromEventFlow (banachContractionToEventFlow x) =
        banachContractionFromEventFlow (banachContractionToEventFlow y) :=
    congrArg banachContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachContractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachContractionTasteGate_single_carrier_alignment_round_trip y)))

instance banachContractionBHistCarrier : BHistCarrier BanachContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachContractionToEventFlow
  fromEventFlow := banachContractionFromEventFlow

instance banachContractionChapterTasteGate : ChapterTasteGate BanachContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachContractionFromEventFlow (banachContractionToEventFlow x) = some x
    exact BanachContractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachContractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BanachContractionTasteGate_single_carrier_alignment :
    (forall h : BHist, banachContractionDecodeBHist (banachContractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BanachContractionUp) ∧
        Nonempty (ChapterTasteGate BanachContractionUp) ∧
          banachContractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BanachContractionTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro banachContractionBHistCarrier,
      Nonempty.intro banachContractionChapterTasteGate,
      rfl⟩

end BEDC.Derived.BanachContractionUp
