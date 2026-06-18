import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopMetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

theorem BishopMetricCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M E Q W S R T H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory Q ∧ UnaryHistory W ∧
      UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont M E Q ∧
          Cont Q W S ∧ Cont S R T ∧ Cont H C P ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧ UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory Q ∧
            UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory T ∧
              UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
                Cont M E Q ∧ Cont Q W S ∧ Cont S R T ∧ Cont H C P ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        (fun row : BHist =>
          hsame row N ∧ Cont M E Q ∧ Cont Q W S ∧ Cont S R T)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro obligations
  obtain ⟨hM, hE, hQ, hW, hS, hR, hT, hH, hC, hP, hN, hMEQ, hQWS, hSRT, hHCP,
    hPpkg, hNpkg⟩ := obligations
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N
          ⟨hsame_refl N, hM, hE, hQ, hW, hS, hR, hT, hH, hC, hP, hN, hMEQ,
            hQWS, hSRT, hHCP, hPpkg, hNpkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      obtain ⟨same, _hM, _hE, _hQ, _hW, _hS, _hR, _hT, _hH, _hC, _hP, _hN, hMEQ,
        hQWS, hSRT, _hHCP, _hPpkg, _hNpkg⟩ := source
      exact ⟨same, hMEQ, hQWS, hSRT⟩
    ledger_sound := by
      intro _row source
      obtain ⟨same, _hM, _hE, _hQ, _hW, _hS, _hR, _hT, _hH, _hC, _hP, hN, _hMEQ,
        _hQWS, _hSRT, _hHCP, _hPpkg, hNpkg⟩ := source
      exact ⟨unary_transport hN (hsame_symm same), hNpkg⟩
  }

inductive BishopMetricCompletionUp : Type where
  | mk (M E Q W S R T H C P N : BHist) : BishopMetricCompletionUp
  deriving DecidableEq

def bishopMetricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopMetricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopMetricCompletionEncodeBHist h

def bishopMetricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopMetricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopMetricCompletionDecodeBHist tail)

private theorem BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopMetricCompletionFields : BishopMetricCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopMetricCompletionUp.mk M E Q W S R T H C P N => [M, E, Q, W, S, R, T, H, C, P, N]

def bishopMetricCompletionToEventFlow : BishopMetricCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopMetricCompletionFields x).map bishopMetricCompletionEncodeBHist

private def bishopMetricCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopMetricCompletionEventAtDefault index rest

def bishopMetricCompletionFromEventFlow (ef : EventFlow) : Option BishopMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopMetricCompletionUp.mk
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 0 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 1 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 2 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 3 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 4 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 5 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 6 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 7 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 8 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 9 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 10 ef)))

private theorem BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopMetricCompletionUp,
      bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E Q W S R T H C P N =>
      change
        some
          (BishopMetricCompletionUp.mk
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist M))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist E))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist Q))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist W))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist S))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist R))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist T))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist H))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist C))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist P))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist N))) =
          some (BishopMetricCompletionUp.mk M E Q W S R T H C P N)
      rw [BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode M,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode W,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode T,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopMetricCompletionUp} :
    bishopMetricCompletionToEventFlow x = bishopMetricCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow x) =
        bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow y) :=
    congrArg bishopMetricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopMetricCompletionBHistCarrier : BHistCarrier BishopMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopMetricCompletionToEventFlow
  fromEventFlow := bishopMetricCompletionFromEventFlow

instance bishopMetricCompletionChapterTasteGate :
    ChapterTasteGate BishopMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow x) = some x
    exact BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopMetricCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BishopMetricCompletionUp) ∧
      Nonempty (ChapterTasteGate BishopMetricCompletionUp) ∧
        bishopMetricCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨bishopMetricCompletionBHistCarrier⟩
  constructor
  · exact ⟨bishopMetricCompletionChapterTasteGate⟩
  · rfl

end BEDC.Derived.BishopMetricCompletionUp
