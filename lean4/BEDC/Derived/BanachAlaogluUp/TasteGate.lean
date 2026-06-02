import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachAlaogluUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachAlaogluUp : Type where
  | mk (B L W S R F T C P N : BHist) : BanachAlaogluUp
  deriving DecidableEq

def banachAlaogluEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachAlaogluEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachAlaogluEncodeBHist h

def banachAlaogluDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachAlaogluDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachAlaogluDecodeBHist tail)

private theorem BanachAlaogluTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, banachAlaogluDecodeBHist (banachAlaogluEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachAlaogluFields : BanachAlaogluUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachAlaogluUp.mk B L W S R F T C P N => [B, L, W, S, R, F, T, C, P, N]

def banachAlaogluToEventFlow : BanachAlaogluUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (banachAlaogluFields x).map banachAlaogluEncodeBHist

private def banachAlaogluEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachAlaogluEventAtDefault index rest

def banachAlaogluFromEventFlow (ef : EventFlow) : Option BanachAlaogluUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachAlaogluUp.mk
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 0 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 1 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 2 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 3 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 4 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 5 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 6 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 7 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 8 ef))
      (banachAlaogluDecodeBHist (banachAlaogluEventAtDefault 9 ef)))

private theorem BanachAlaogluTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachAlaogluUp,
      banachAlaogluFromEventFlow (banachAlaogluToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L W S R F T C P N =>
      change
        some
          (BanachAlaogluUp.mk
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist B))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist L))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist W))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist S))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist R))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist F))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist T))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist C))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist P))
            (banachAlaogluDecodeBHist (banachAlaogluEncodeBHist N))) =
          some (BanachAlaogluUp.mk B L W S R F T C P N)
      rw [BanachAlaogluTasteGate_single_carrier_alignment_decode B,
        BanachAlaogluTasteGate_single_carrier_alignment_decode L,
        BanachAlaogluTasteGate_single_carrier_alignment_decode W,
        BanachAlaogluTasteGate_single_carrier_alignment_decode S,
        BanachAlaogluTasteGate_single_carrier_alignment_decode R,
        BanachAlaogluTasteGate_single_carrier_alignment_decode F,
        BanachAlaogluTasteGate_single_carrier_alignment_decode T,
        BanachAlaogluTasteGate_single_carrier_alignment_decode C,
        BanachAlaogluTasteGate_single_carrier_alignment_decode P,
        BanachAlaogluTasteGate_single_carrier_alignment_decode N]

private theorem BanachAlaogluTasteGate_single_carrier_alignment_injective
    {x y : BanachAlaogluUp} :
    banachAlaogluToEventFlow x = banachAlaogluToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachAlaogluFromEventFlow (banachAlaogluToEventFlow x) =
        banachAlaogluFromEventFlow (banachAlaogluToEventFlow y) :=
    congrArg banachAlaogluFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BanachAlaogluTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BanachAlaogluTasteGate_single_carrier_alignment_round_trip y)))

instance banachAlaogluBHistCarrier : BHistCarrier BanachAlaogluUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachAlaogluToEventFlow
  fromEventFlow := banachAlaogluFromEventFlow

instance banachAlaogluChapterTasteGate : ChapterTasteGate BanachAlaogluUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachAlaogluFromEventFlow (banachAlaogluToEventFlow x) = some x
    exact BanachAlaogluTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachAlaogluTasteGate_single_carrier_alignment_injective heq)

instance banachAlaogluNontrivial : Nontrivial BanachAlaogluUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachAlaogluUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BanachAlaogluUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachAlaogluUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachAlaogluChapterTasteGate

theorem BanachAlaogluTasteGate_single_carrier_alignment :
    (∀ h : BHist, banachAlaogluDecodeBHist (banachAlaogluEncodeBHist h) = h) ∧
      (∀ x : BanachAlaogluUp,
        banachAlaogluFromEventFlow (banachAlaogluToEventFlow x) = some x) ∧
        (∀ x y : BanachAlaogluUp,
          banachAlaogluToEventFlow x = banachAlaogluToEventFlow y → x = y) ∧
          banachAlaogluEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Nontrivial
  exact
    ⟨BanachAlaogluTasteGate_single_carrier_alignment_decode,
      BanachAlaogluTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BanachAlaogluTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BanachAlaogluUp
