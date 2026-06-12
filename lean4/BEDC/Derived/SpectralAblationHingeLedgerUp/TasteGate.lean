import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpectralAblationHingeLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpectralAblationHingeLedgerUp : Type where
  | mk (M O A E H R T C P N : BHist) : SpectralAblationHingeLedgerUp
  deriving DecidableEq

private def spectralAblationHingeLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spectralAblationHingeLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spectralAblationHingeLedgerEncodeBHist h

private def spectralAblationHingeLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spectralAblationHingeLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spectralAblationHingeLedgerDecodeBHist tail)

private theorem spectralAblationHingeLedger_decode_encode_bhist :
    ∀ h : BHist,
      spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def spectralAblationHingeLedgerFields :
    SpectralAblationHingeLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpectralAblationHingeLedgerUp.mk M O A E H R T C P N => [M, O, A, E, H, R, T, C, P, N]

private def spectralAblationHingeLedgerToEventFlow :
    SpectralAblationHingeLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (spectralAblationHingeLedgerFields x).map spectralAblationHingeLedgerEncodeBHist

private def spectralAblationHingeLedgerEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => spectralAblationHingeLedgerEventAtDefault index rest

private def spectralAblationHingeLedgerFromEventFlow
    (ef : EventFlow) : Option SpectralAblationHingeLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SpectralAblationHingeLedgerUp.mk
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 0 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 1 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 2 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 3 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 4 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 5 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 6 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 7 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 8 ef))
      (spectralAblationHingeLedgerDecodeBHist
        (spectralAblationHingeLedgerEventAtDefault 9 ef)))

private theorem spectralAblationHingeLedger_round_trip :
    ∀ x : SpectralAblationHingeLedgerUp,
      spectralAblationHingeLedgerFromEventFlow
        (spectralAblationHingeLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M O A E H R T C P N =>
      change
        some
          (SpectralAblationHingeLedgerUp.mk
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist M))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist O))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist A))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist E))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist H))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist R))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist T))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist C))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist P))
            (spectralAblationHingeLedgerDecodeBHist
              (spectralAblationHingeLedgerEncodeBHist N))) =
          some (SpectralAblationHingeLedgerUp.mk M O A E H R T C P N)
      rw [spectralAblationHingeLedger_decode_encode_bhist M,
        spectralAblationHingeLedger_decode_encode_bhist O,
        spectralAblationHingeLedger_decode_encode_bhist A,
        spectralAblationHingeLedger_decode_encode_bhist E,
        spectralAblationHingeLedger_decode_encode_bhist H,
        spectralAblationHingeLedger_decode_encode_bhist R,
        spectralAblationHingeLedger_decode_encode_bhist T,
        spectralAblationHingeLedger_decode_encode_bhist C,
        spectralAblationHingeLedger_decode_encode_bhist P,
        spectralAblationHingeLedger_decode_encode_bhist N]

private theorem spectralAblationHingeLedgerToEventFlow_injective
    {x y : SpectralAblationHingeLedgerUp} :
    spectralAblationHingeLedgerToEventFlow x =
      spectralAblationHingeLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spectralAblationHingeLedgerFromEventFlow (spectralAblationHingeLedgerToEventFlow x) =
        spectralAblationHingeLedgerFromEventFlow (spectralAblationHingeLedgerToEventFlow y) :=
    congrArg spectralAblationHingeLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (spectralAblationHingeLedger_round_trip x).symm
      (Eq.trans hread (spectralAblationHingeLedger_round_trip y)))

private theorem spectralAblationHingeLedger_fields_faithful :
    ∀ x y : SpectralAblationHingeLedgerUp,
      spectralAblationHingeLedgerFields x =
        spectralAblationHingeLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ O₁ A₁ E₁ H₁ R₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ O₂ A₂ E₂ H₂ R₂ T₂ C₂ P₂ N₂ =>
          injection hfields with hM rest₁
          injection rest₁ with hO rest₂
          injection rest₂ with hA rest₃
          injection rest₃ with hE rest₄
          injection rest₄ with hH rest₅
          injection rest₅ with hR rest₆
          injection rest₆ with hT rest₇
          injection rest₇ with hC rest₈
          injection rest₈ with hP rest₉
          injection rest₉ with hN _
          cases hM
          cases hO
          cases hA
          cases hE
          cases hH
          cases hR
          cases hT
          cases hC
          cases hP
          cases hN
          rfl

instance spectralAblationHingeLedgerBHistCarrier :
    BHistCarrier SpectralAblationHingeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spectralAblationHingeLedgerToEventFlow
  fromEventFlow := spectralAblationHingeLedgerFromEventFlow

instance spectralAblationHingeLedgerChapterTasteGate :
    ChapterTasteGate SpectralAblationHingeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      spectralAblationHingeLedgerFromEventFlow
        (spectralAblationHingeLedgerToEventFlow x) = some x
    exact spectralAblationHingeLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (spectralAblationHingeLedgerToEventFlow_injective heq)

instance spectralAblationHingeLedgerFieldFaithful :
    FieldFaithful SpectralAblationHingeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := spectralAblationHingeLedgerFields
  field_faithful := spectralAblationHingeLedger_fields_faithful

instance spectralAblationHingeLedgerNontrivial :
    Nontrivial SpectralAblationHingeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SpectralAblationHingeLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SpectralAblationHingeLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hM _ _ _ _ _ _ _ _ _
        cases hM⟩

theorem SpectralAblationHingeLedgerTasteGate_single_carrier_alignment :
    ChapterTasteGate SpectralAblationHingeLedgerUp := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact spectralAblationHingeLedgerChapterTasteGate

end BEDC.Derived.SpectralAblationHingeLedgerUp
