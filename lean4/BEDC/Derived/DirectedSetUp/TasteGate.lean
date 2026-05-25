import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirectedSetUp

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

inductive DirectedSetUp : Type where
  | mk (I Le W U H C P N : BHist) : DirectedSetUp
  deriving DecidableEq

def directedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: directedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: directedSetEncodeBHist h

def directedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (directedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (directedSetDecodeBHist tail)

private theorem DirectedSetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, directedSetDecodeBHist (directedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def directedSetFields : DirectedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirectedSetUp.mk I Le W U H C P N => [I, Le, W, U, H, C, P, N]

def directedSetToEventFlow : DirectedSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map directedSetEncodeBHist (directedSetFields x)

private def directedSetRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => directedSetRawAt index rest

def directedSetFromEventFlow (flow : EventFlow) : Option DirectedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DirectedSetUp.mk
      (directedSetDecodeBHist (directedSetRawAt 0 flow))
      (directedSetDecodeBHist (directedSetRawAt 1 flow))
      (directedSetDecodeBHist (directedSetRawAt 2 flow))
      (directedSetDecodeBHist (directedSetRawAt 3 flow))
      (directedSetDecodeBHist (directedSetRawAt 4 flow))
      (directedSetDecodeBHist (directedSetRawAt 5 flow))
      (directedSetDecodeBHist (directedSetRawAt 6 flow))
      (directedSetDecodeBHist (directedSetRawAt 7 flow)))

private theorem DirectedSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DirectedSetUp, directedSetFromEventFlow (directedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Le W U H C P N =>
      change
        some
          (DirectedSetUp.mk
            (directedSetDecodeBHist (directedSetEncodeBHist I))
            (directedSetDecodeBHist (directedSetEncodeBHist Le))
            (directedSetDecodeBHist (directedSetEncodeBHist W))
            (directedSetDecodeBHist (directedSetEncodeBHist U))
            (directedSetDecodeBHist (directedSetEncodeBHist H))
            (directedSetDecodeBHist (directedSetEncodeBHist C))
            (directedSetDecodeBHist (directedSetEncodeBHist P))
            (directedSetDecodeBHist (directedSetEncodeBHist N))) =
          some (DirectedSetUp.mk I Le W U H C P N)
      rw [DirectedSetTasteGate_single_carrier_alignment_decode I,
        DirectedSetTasteGate_single_carrier_alignment_decode Le,
        DirectedSetTasteGate_single_carrier_alignment_decode W,
        DirectedSetTasteGate_single_carrier_alignment_decode U,
        DirectedSetTasteGate_single_carrier_alignment_decode H,
        DirectedSetTasteGate_single_carrier_alignment_decode C,
        DirectedSetTasteGate_single_carrier_alignment_decode P,
        DirectedSetTasteGate_single_carrier_alignment_decode N]

private theorem directedSetToEventFlow_injective {x y : DirectedSetUp} :
    directedSetToEventFlow x = directedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      directedSetFromEventFlow (directedSetToEventFlow x) =
        directedSetFromEventFlow (directedSetToEventFlow y) :=
    congrArg directedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DirectedSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DirectedSetTasteGate_single_carrier_alignment_round_trip y)))

instance directedSetBHistCarrier : BHistCarrier DirectedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := directedSetToEventFlow
  fromEventFlow := directedSetFromEventFlow

instance directedSetChapterTasteGate : ChapterTasteGate DirectedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change directedSetFromEventFlow (directedSetToEventFlow x) = some x
    exact DirectedSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (directedSetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DirectedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  directedSetChapterTasteGate

theorem DirectedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, directedSetDecodeBHist (directedSetEncodeBHist h) = h) ∧
      (∀ x : DirectedSetUp, directedSetFromEventFlow (directedSetToEventFlow x) = some x) ∧
        (∀ x y : DirectedSetUp, directedSetToEventFlow x = directedSetToEventFlow y → x = y) ∧
          directedSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DirectedSetTasteGate_single_carrier_alignment_decode,
      DirectedSetTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact directedSetToEventFlow_injective heq,
      rfl⟩

theorem DirectedSet_cauchynet_index_handoff_certificate [AskSetup] [PackageSetup]
    {I Le W U H C P N cauchyWindow limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I W cauchyWindow →
      Cont U H limitRead →
        PkgSig bundle P pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row cauchyWindow ∧
                  directedSetFields (DirectedSetUp.mk I Le W U H C P N) =
                    [I, Le, W, U, H, C, P, N])
              (fun row : BHist =>
                hsame row I ∨ hsame row Le ∨ hsame row W ∨ hsame row U ∨
                  hsame row cauchyWindow ∨ hsame row limitRead)
              (fun row : BHist => hsame row cauchyWindow ∧ PkgSig bundle P pkg)
              hsame ∧
            Exists (fun route : BHist => Cont I W route) ∧
              Exists (fun route : BHist => Cont U H route) := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert
  intro cauchyRoute limitRoute pkgSig
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cauchyWindow ∧
              directedSetFields (DirectedSetUp.mk I Le W U H C P N) =
                [I, Le, W, U, H, C, P, N])
          (fun row : BHist =>
            hsame row I ∨ hsame row Le ∨ hsame row W ∨ hsame row U ∨
              hsame row cauchyWindow ∨ hsame row limitRead)
          (fun row : BHist => hsame row cauchyWindow ∧ PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro cauchyWindow ⟨hsame_refl cauchyWindow, rfl⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, ⟨cauchyWindow, cauchyRoute⟩, ⟨limitRead, limitRoute⟩⟩

def DirectedSetPacket [AskSetup] [PackageSetup]
    (I Le W U H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory I ∧ UnaryHistory Le ∧ UnaryHistory W ∧ UnaryHistory U ∧
    (∀ {window witness : BHist}, Cont W window witness → UnaryHistory window) ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧ Cont W U H ∧
        Cont H C N ∧ PkgSig bundle P pkg

theorem DirectedSetPacket_finite_upper_window_stability [AskSetup] [PackageSetup]
    {I Le W U H C P N retainedWindow retainedWitness retainedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSetPacket I Le W U H C P N bundle pkg →
      Cont W retainedWindow retainedWitness →
        Cont retainedWitness H retainedReplay →
          PkgSig bundle retainedReplay pkg →
            UnaryHistory I ∧ UnaryHistory Le ∧ UnaryHistory W ∧ UnaryHistory U ∧
              UnaryHistory retainedWindow ∧ UnaryHistory retainedWitness ∧
                UnaryHistory retainedReplay ∧ Cont W retainedWindow retainedWitness ∧
                  Cont retainedWitness H retainedReplay ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle retainedReplay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet retainedRoute replayRoute replayPkg
  obtain ⟨iUnary, leUnary, wUnary, uUnary, windowUnary, hUnary, _cUnary, _nUnary,
    _wuh, _hcn, pPkg⟩ := packet
  have retainedWindowUnary : UnaryHistory retainedWindow :=
    windowUnary retainedRoute
  have retainedWitnessUnary : UnaryHistory retainedWitness :=
    unary_cont_closed wUnary retainedWindowUnary retainedRoute
  have replayUnary : UnaryHistory retainedReplay :=
    unary_cont_closed retainedWitnessUnary hUnary replayRoute
  exact
    ⟨iUnary, leUnary, wUnary, uUnary, retainedWindowUnary, retainedWitnessUnary,
      replayUnary, retainedRoute, replayRoute, pPkg, replayPkg⟩

end BEDC.Derived.DirectedSetUp
