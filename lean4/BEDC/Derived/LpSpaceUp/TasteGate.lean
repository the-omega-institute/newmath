import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LpSpaceUp

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

def LpSpaceCarrier [AskSetup] [PackageSetup]
    (M R V N B I E H C Q A : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory V ∧ UnaryHistory N ∧
    UnaryHistory B ∧ UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory A ∧
        PkgSig bundle Q pkg ∧ PkgSig bundle A pkg

theorem LpSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M R V N B I E H C Q A read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LpSpaceCarrier M R V N B I E H C Q A bundle pkg →
      Cont I E read →
        PkgSig bundle read pkg →
          SemanticNameCert
              (fun row : BHist => hsame row read ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row V ∨ hsame row N ∨
                  hsame row B ∨ hsame row I ∨ hsame row E ∨ hsame row read)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont I E read ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle read pkg)
              hsame ∧
            UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier readRoute readPkg
  obtain ⟨_mUnary, _rUnary, _vUnary, _nUnary, _bUnary, iUnary, eUnary, _hUnary,
    _cUnary, _qUnary, _aUnary, qPkg, _aPkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed iUnary eUnary readRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row V ∨ hsame row N ∨
              hsame row B ∨ hsame row I ∨ hsame row E ∨ hsame row read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I E read ∧ PkgSig bundle Q pkg ∧
              PkgSig bundle read pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro read ⟨hsame_refl read, readUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readRoute, qPkg, readPkg⟩
  }
  exact ⟨cert, readUnary⟩

inductive LpSpaceUp : Type where
  | mk (M R V N B I E H C Q A : BHist) : LpSpaceUp
  deriving DecidableEq

def lpSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lpSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lpSpaceEncodeBHist h

def lpSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lpSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lpSpaceDecodeBHist tail)

private theorem LpSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lpSpaceDecodeBHist (lpSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lpSpaceFields : LpSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LpSpaceUp.mk M R V N B I E H C Q A => [M, R, V, N, B, I, E, H, C, Q, A]

def lpSpaceToEventFlow : LpSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lpSpaceFields x).map lpSpaceEncodeBHist

private def lpSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lpSpaceEventAtDefault index rest

def lpSpaceFromEventFlow : EventFlow → Option LpSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LpSpaceUp.mk
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 0 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 1 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 2 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 3 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 4 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 5 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 6 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 7 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 8 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 9 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 10 ef)))

private theorem LpSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LpSpaceUp, lpSpaceFromEventFlow (lpSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R V N B I E H C Q A =>
      change
        some
          (LpSpaceUp.mk
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist M))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist R))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist V))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist N))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist B))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist I))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist E))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist H))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist C))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist Q))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist A))) =
          some (LpSpaceUp.mk M R V N B I E H C Q A)
      rw [LpSpaceTasteGate_single_carrier_alignment_decode M,
        LpSpaceTasteGate_single_carrier_alignment_decode R,
        LpSpaceTasteGate_single_carrier_alignment_decode V,
        LpSpaceTasteGate_single_carrier_alignment_decode N,
        LpSpaceTasteGate_single_carrier_alignment_decode B,
        LpSpaceTasteGate_single_carrier_alignment_decode I,
        LpSpaceTasteGate_single_carrier_alignment_decode E,
        LpSpaceTasteGate_single_carrier_alignment_decode H,
        LpSpaceTasteGate_single_carrier_alignment_decode C,
        LpSpaceTasteGate_single_carrier_alignment_decode Q,
        LpSpaceTasteGate_single_carrier_alignment_decode A]

private theorem LpSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LpSpaceUp} :
    lpSpaceToEventFlow x = lpSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lpSpaceFromEventFlow (lpSpaceToEventFlow x) =
        lpSpaceFromEventFlow (lpSpaceToEventFlow y) :=
    congrArg lpSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LpSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LpSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance lpSpaceBHistCarrier : BHistCarrier LpSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lpSpaceToEventFlow
  fromEventFlow := lpSpaceFromEventFlow

instance lpSpaceChapterTasteGate : ChapterTasteGate LpSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lpSpaceFromEventFlow (lpSpaceToEventFlow x) = some x
    exact LpSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LpSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LpSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lpSpaceChapterTasteGate

theorem LpSpaceTasteGate_single_carrier_alignment :
    (∃ x : LpSpaceUp,
        lpSpaceFields x =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty]) ∧
      Nonempty (BHistCarrier LpSpaceUp) ∧ Nonempty (ChapterTasteGate LpSpaceUp) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨LpSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩,
      ⟨lpSpaceBHistCarrier⟩, ⟨lpSpaceChapterTasteGate⟩⟩

end BEDC.Derived.LpSpaceUp
