import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchySequenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchySequenceUp : Type where
  | mk (S M W D Q E H C P N : BHist) : EffectiveCauchySequenceUp
  deriving DecidableEq

def effectiveCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchySequenceEncodeBHist h

def effectiveCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchySequenceDecodeBHist tail)

private theorem effectiveCauchySequence_decode_encode :
    ∀ h : BHist,
      effectiveCauchySequenceDecodeBHist
          (effectiveCauchySequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchySequenceFields :
    EffectiveCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchySequenceUp.mk S M W D Q E H C P N =>
      [S, M, W, D, Q, E, H, C, P, N]

def effectiveCauchySequenceToEventFlow :
    EffectiveCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map effectiveCauchySequenceEncodeBHist
        (effectiveCauchySequenceFields x)

private def effectiveCauchySequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveCauchySequenceRawAt index rest

def effectiveCauchySequenceFromEventFlow
    (flow : EventFlow) : Option EffectiveCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveCauchySequenceUp.mk
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 0 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 1 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 2 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 3 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 4 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 5 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 6 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 7 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 8 flow))
      (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceRawAt 9 flow)))

private theorem effectiveCauchySequence_round_trip :
    ∀ x : EffectiveCauchySequenceUp,
      effectiveCauchySequenceFromEventFlow
          (effectiveCauchySequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W D Q E H C P N =>
      change
        some
          (EffectiveCauchySequenceUp.mk
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist S))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist M))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist W))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist D))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist Q))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist E))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist H))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist C))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist P))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist N))) =
          some (EffectiveCauchySequenceUp.mk S M W D Q E H C P N)
      rw [effectiveCauchySequence_decode_encode S,
        effectiveCauchySequence_decode_encode M,
        effectiveCauchySequence_decode_encode W,
        effectiveCauchySequence_decode_encode D,
        effectiveCauchySequence_decode_encode Q,
        effectiveCauchySequence_decode_encode E,
        effectiveCauchySequence_decode_encode H,
        effectiveCauchySequence_decode_encode C,
        effectiveCauchySequence_decode_encode P,
        effectiveCauchySequence_decode_encode N]

private theorem effectiveCauchySequenceToEventFlow_injective
    {x y : EffectiveCauchySequenceUp} :
    effectiveCauchySequenceToEventFlow x =
        effectiveCauchySequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchySequenceFromEventFlow
          (effectiveCauchySequenceToEventFlow x) =
        effectiveCauchySequenceFromEventFlow
          (effectiveCauchySequenceToEventFlow y) :=
    congrArg effectiveCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveCauchySequence_round_trip x).symm
      (Eq.trans hread (effectiveCauchySequence_round_trip y)))

instance effectiveCauchySequenceBHistCarrier :
    BHistCarrier EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchySequenceToEventFlow
  fromEventFlow := effectiveCauchySequenceFromEventFlow

instance effectiveCauchySequenceChapterTasteGate :
    ChapterTasteGate EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      effectiveCauchySequenceFromEventFlow
          (effectiveCauchySequenceToEventFlow x) =
        some x
    exact effectiveCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveCauchySequenceToEventFlow_injective heq)

instance effectiveCauchySequenceFieldFaithful :
    FieldFaithful EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveCauchySequenceFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ M₁ W₁ D₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ W₂ D₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
        injection h with hS t1
        injection t1 with hM t2
        injection t2 with hW t3
        injection t3 with hD t4
        injection t4 with hQ t5
        injection t5 with hE t6
        injection t6 with hH t7
        injection t7 with hC t8
        injection t8 with hP t9
        injection t9 with hN _
        cases hS
        cases hM
        cases hW
        cases hD
        cases hQ
        cases hE
        cases hH
        cases hC
        cases hP
        cases hN
        rfl

def taste_gate : ChapterTasteGate EffectiveCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCauchySequenceChapterTasteGate

theorem EffectiveCauchySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveCauchySequenceDecodeBHist
          (effectiveCauchySequenceEncodeBHist h) =
        h) ∧
      (∀ x : EffectiveCauchySequenceUp,
        effectiveCauchySequenceFromEventFlow
            (effectiveCauchySequenceToEventFlow x) =
          some x) ∧
        (∀ x y : EffectiveCauchySequenceUp,
          effectiveCauchySequenceToEventFlow x =
              effectiveCauchySequenceToEventFlow y →
            x = y) ∧
          effectiveCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨effectiveCauchySequence_decode_encode,
      effectiveCauchySequence_round_trip,
      by
        intro x y heq
        exact effectiveCauchySequenceToEventFlow_injective heq,
      rfl⟩

theorem EffectiveCauchySequenceCarrier_namecert_obligations
    (x : EffectiveCauchySequenceUp) :
    SemanticNameCert
      (fun row : BHist =>
        exists S M W D Q E H C P N : BHist,
          x = EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧ hsame row N)
      (fun row : BHist =>
        exists S M W D Q E H C P N : BHist,
          x = EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧ hsame row N)
      (fun row : BHist =>
        exists S M W D Q E H C P N : BHist,
          x = EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk S M W D Q E H C P N =>
      have core :
          NameCert
            (fun row : BHist =>
              exists S' M' W' D' Q' E' H' C' P' N' : BHist,
                EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                    EffectiveCauchySequenceUp.mk S' M' W' D' Q' E' H' C' P' N' ∧
                  hsame row N')
            hsame := {
        carrier_inhabited := by
          exact ⟨N, S, M, W, D, Q, E, H, C, P, N, rfl, hsame_refl N⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          cases sameRows
          exact source
      }
      exact {
        core := core
        pattern_sound := by
          intro row source
          exact source
        ledger_sound := by
          intro row source
          exact source
      }

theorem EffectiveCauchySequenceCarrier_regseqrat_handoff
    {S M W D Q E H C P N readM readW readD readQ : BHist} :
    Cont S M readM ->
      Cont readM W readW ->
        Cont readW D readD ->
          Cont readD Q readQ ->
            UnaryHistory S ->
              UnaryHistory M ->
                UnaryHistory W ->
                  UnaryHistory D ->
                    UnaryHistory Q ->
                      UnaryHistory readM ∧ UnaryHistory readW ∧ UnaryHistory readD ∧
                        UnaryHistory readQ ∧ Cont S M readM ∧ Cont readM W readW ∧
                          Cont readW D readD ∧ Cont readD Q readQ := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro routeM routeW routeD routeQ unaryS unaryM unaryW unaryD unaryQ
  have unaryReadM : UnaryHistory readM :=
    unary_cont_closed unaryS unaryM routeM
  have unaryReadW : UnaryHistory readW :=
    unary_cont_closed unaryReadM unaryW routeW
  have unaryReadD : UnaryHistory readD :=
    unary_cont_closed unaryReadW unaryD routeD
  have unaryReadQ : UnaryHistory readQ :=
    unary_cont_closed unaryReadD unaryQ routeQ
  exact
    ⟨unaryReadM, unaryReadW, unaryReadD, unaryReadQ, routeM, routeW, routeD,
      routeQ⟩

namespace TasteGate

theorem EffectiveCauchySequenceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveCauchySequenceDecodeBHist
          (effectiveCauchySequenceEncodeBHist h) =
        h) ∧
      (∀ x : EffectiveCauchySequenceUp,
        effectiveCauchySequenceFromEventFlow
            (effectiveCauchySequenceToEventFlow x) =
          some x) ∧
        (∀ x y : EffectiveCauchySequenceUp,
          effectiveCauchySequenceToEventFlow x =
              effectiveCauchySequenceToEventFlow y →
            x = y) ∧
          effectiveCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact EffectiveCauchySequenceTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.EffectiveCauchySequenceUp
