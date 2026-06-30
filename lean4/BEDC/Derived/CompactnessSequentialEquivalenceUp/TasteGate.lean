import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactnessSequentialEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactnessSequentialEquivalenceUp : Type where
  | mk
      (K F B S W R D Q H C P N : BHist) :
      CompactnessSequentialEquivalenceUp
  deriving DecidableEq

def compactnessSequentialEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactnessSequentialEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactnessSequentialEquivalenceEncodeBHist h

def compactnessSequentialEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactnessSequentialEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactnessSequentialEquivalenceDecodeBHist tail)

private theorem compactnessSequentialEquivalenceDecode_encode_bhist :
    ∀ h : BHist,
      compactnessSequentialEquivalenceDecodeBHist
          (compactnessSequentialEquivalenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactnessSequentialEquivalenceFields :
    CompactnessSequentialEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactnessSequentialEquivalenceUp.mk K F B S W R D Q H C P N =>
      [K, F, B, S, W, R, D, Q, H, C, P, N]

def compactnessSequentialEquivalenceToEventFlow :
    CompactnessSequentialEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactnessSequentialEquivalenceUp.mk K F B S W R D Q H C P N =>
      [[BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist K,
        [BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactnessSequentialEquivalenceEncodeBHist N]

private def compactnessSequentialEquivalenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactnessSequentialEquivalenceEventAtDefault index rest

def compactnessSequentialEquivalenceFromEventFlow :
    EventFlow → Option CompactnessSequentialEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CompactnessSequentialEquivalenceUp.mk
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 1 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 3 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 5 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 7 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 9 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 11 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 13 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 15 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 17 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 19 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 21 ef))
          (compactnessSequentialEquivalenceDecodeBHist
            (compactnessSequentialEquivalenceEventAtDefault 23 ef)))

private theorem compactnessSequentialEquivalence_round_trip :
    ∀ x : CompactnessSequentialEquivalenceUp,
      compactnessSequentialEquivalenceFromEventFlow
          (compactnessSequentialEquivalenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F B S W R D Q H C P N =>
      change
        some
          (CompactnessSequentialEquivalenceUp.mk
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist K))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist F))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist B))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist S))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist W))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist R))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist D))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist Q))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist H))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist C))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist P))
            (compactnessSequentialEquivalenceDecodeBHist
              (compactnessSequentialEquivalenceEncodeBHist N))) =
          some (CompactnessSequentialEquivalenceUp.mk K F B S W R D Q H C P N)
      rw [compactnessSequentialEquivalenceDecode_encode_bhist K,
        compactnessSequentialEquivalenceDecode_encode_bhist F,
        compactnessSequentialEquivalenceDecode_encode_bhist B,
        compactnessSequentialEquivalenceDecode_encode_bhist S,
        compactnessSequentialEquivalenceDecode_encode_bhist W,
        compactnessSequentialEquivalenceDecode_encode_bhist R,
        compactnessSequentialEquivalenceDecode_encode_bhist D,
        compactnessSequentialEquivalenceDecode_encode_bhist Q,
        compactnessSequentialEquivalenceDecode_encode_bhist H,
        compactnessSequentialEquivalenceDecode_encode_bhist C,
        compactnessSequentialEquivalenceDecode_encode_bhist P,
        compactnessSequentialEquivalenceDecode_encode_bhist N]

private theorem compactnessSequentialEquivalenceToEventFlow_injective
    {x y : CompactnessSequentialEquivalenceUp} :
    compactnessSequentialEquivalenceToEventFlow x =
        compactnessSequentialEquivalenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactnessSequentialEquivalenceFromEventFlow
          (compactnessSequentialEquivalenceToEventFlow x) =
        compactnessSequentialEquivalenceFromEventFlow
          (compactnessSequentialEquivalenceToEventFlow y) :=
    congrArg compactnessSequentialEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactnessSequentialEquivalence_round_trip x).symm
      (Eq.trans hread (compactnessSequentialEquivalence_round_trip y)))

instance compactnessSequentialEquivalenceBHistCarrier :
    BHistCarrier CompactnessSequentialEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactnessSequentialEquivalenceToEventFlow
  fromEventFlow := compactnessSequentialEquivalenceFromEventFlow

instance compactnessSequentialEquivalenceChapterTasteGate :
    ChapterTasteGate CompactnessSequentialEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactnessSequentialEquivalenceFromEventFlow
          (compactnessSequentialEquivalenceToEventFlow x) =
        some x
    exact compactnessSequentialEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactnessSequentialEquivalenceToEventFlow_injective heq)

theorem CompactnessSequentialEquivalenceCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {K F B S W R D Q H C P N coverRead sequenceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    compactnessSequentialEquivalenceFields
        (CompactnessSequentialEquivalenceUp.mk K F B S W R D Q H C P N) =
        [K, F, B, S, W, R, D, Q, H, C, P, N] →
      Cont K F coverRead →
        Cont B S sequenceRead →
          Cont D Q sealRead →
            Cont H C P →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row sealRead ∧
                        ∃ packet : CompactnessSequentialEquivalenceUp,
                          packet =
                              CompactnessSequentialEquivalenceUp.mk
                                K F B S W R D Q H C P N ∧
                            compactnessSequentialEquivalenceFields packet =
                              [K, F, B, S, W, R, D, Q, H, C, P, N])
                    (fun row : BHist =>
                      hsame row sealRead ∧ Cont K F coverRead ∧
                        Cont B S sequenceRead)
                    (fun row : BHist =>
                      hsame row sealRead ∧ Cont D Q sealRead ∧ Cont H C P ∧
                        PkgSig bundle N pkg)
                    hsame ∧
                  compactnessSequentialEquivalenceFields
                      (CompactnessSequentialEquivalenceUp.mk K F B S W R D Q H C P N) =
                    [K, F, B, S, W, R, D, Q, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact coverRoute sequenceRoute sealRoute replayRoute packageName
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨sealRead, hsame_refl sealRead,
              CompactnessSequentialEquivalenceUp.mk K F B S W R D Q H C P N,
              rfl, fieldsExact⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨source.left, coverRoute, sequenceRoute⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, sealRoute, replayRoute, packageName⟩
    }
  · exact fieldsExact

namespace TasteGate

theorem CompactnessSequentialEquivalenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactnessSequentialEquivalenceUp) ∧
      Cont BHist.Empty BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark Cont ChapterTasteGate
  constructor
  · exact ⟨compactnessSequentialEquivalenceChapterTasteGate⟩
  · rfl

end TasteGate

end BEDC.Derived.CompactnessSequentialEquivalenceUp
