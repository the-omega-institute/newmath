import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyReblockingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyReblockingUp : Type where
  | mk (R W K T D L H C P N : BHist) : BishopCauchyReblockingUp
  deriving DecidableEq

def bishopCauchyReblockingFields : BishopCauchyReblockingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyReblockingUp.mk R W K T D L H C P N =>
      [R, W, K, T, D, L, H, C, P, N]

private def BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist h

private def BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist tail)

private theorem BishopCauchyReblockingCarrier_namecert_obligations_decode_encode
    (h : BHist) :
    BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow :
    BishopCauchyReblockingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopCauchyReblockingFields x).map
        BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist

private def BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault index rest

private def BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow
    (ef : EventFlow) :
    Option BishopCauchyReblockingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyReblockingUp.mk
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 0 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 1 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 2 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 3 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 4 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 5 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 6 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 7 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 8 ef))
      (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
        (BishopCauchyReblockingCarrier_namecert_obligations_eventAtDefault 9 ef)))

private theorem BishopCauchyReblockingCarrier_namecert_obligations_round_trip
    (x : BishopCauchyReblockingUp) :
    BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow
        (BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R W K T D L H C P N =>
      change
        some
          (BishopCauchyReblockingUp.mk
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist R))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist W))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist K))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist T))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist D))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist L))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist H))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist C))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist P))
            (BishopCauchyReblockingCarrier_namecert_obligations_decodeBHist
              (BishopCauchyReblockingCarrier_namecert_obligations_encodeBHist N))) =
          some (BishopCauchyReblockingUp.mk R W K T D L H C P N)
      rw [BishopCauchyReblockingCarrier_namecert_obligations_decode_encode R,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode W,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode K,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode T,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode D,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode L,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode H,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode C,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode P,
        BishopCauchyReblockingCarrier_namecert_obligations_decode_encode N]

private theorem BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow_injective
    {x y : BishopCauchyReblockingUp} :
    BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow x =
      BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow
          (BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow x) =
        BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow
          (BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow y) :=
    congrArg BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyReblockingCarrier_namecert_obligations_round_trip x).symm
      (Eq.trans hread (BishopCauchyReblockingCarrier_namecert_obligations_round_trip y)))

instance bishopCauchyReblockingBHistCarrier : BHistCarrier BishopCauchyReblockingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow
  fromEventFlow := BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow

instance bishopCauchyReblockingChapterTasteGate :
    ChapterTasteGate BishopCauchyReblockingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopCauchyReblockingCarrier_namecert_obligations_fromEventFlow
          (BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow x) = some x
    exact BishopCauchyReblockingCarrier_namecert_obligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCauchyReblockingCarrier_namecert_obligations_toEventFlow_injective heq)

theorem BishopCauchyReblockingCarrier_namecert_obligations
    (x : BishopCauchyReblockingUp) :
    exists R W K T D L H C P N replay sealRow : BHist,
      bishopCauchyReblockingFields x = [R, W, K, T, D, L, H, C, P, N] ∧
        Cont R W replay ∧ Cont replay D sealRow ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) ∧
            Nonempty (NameCert (fun h : BHist => hsame h sealRow) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk R W K T D L H C P N =>
      refine ⟨R, W, K, T, D, L, H, C, P, N, append R W, append (append R W) D, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      constructor
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro N (hsame_refl N)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro row other same
              exact hsame_symm same
            equiv_trans := by
              intro row other third sameRO sameOT
              exact hsame_trans sameRO sameOT
            carrier_respects_equiv := by
              intro row other same source
              exact hsame_trans (hsame_symm same) source
          }
      · exact
          Nonempty.intro {
            carrier_inhabited :=
              Exists.intro (append (append R W) D) (hsame_refl (append (append R W) D))
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro row other same
              exact hsame_symm same
            equiv_trans := by
              intro row other third sameRO sameOT
              exact hsame_trans sameRO sameOT
            carrier_respects_equiv := by
              intro row other same source
              exact hsame_trans (hsame_symm same) source
          }

end BEDC.Derived.BishopCauchyReblockingUp
