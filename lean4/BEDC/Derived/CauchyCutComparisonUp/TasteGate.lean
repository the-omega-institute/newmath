import BEDC.Derived.CauchyCutComparisonUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCutComparisonUp

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

inductive CauchyCutComparisonUp : Type where
  | mk (K Q S R D A H C P N : BHist) : CauchyCutComparisonUp
  deriving DecidableEq

def cauchyCutComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCutComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCutComparisonEncodeBHist h

def cauchyCutComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCutComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCutComparisonDecodeBHist tail)

private theorem CauchyCutComparisonTasteGate_decode_encode :
    ∀ h : BHist, cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCutComparisonFields : CauchyCutComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCutComparisonUp.mk K Q S R D A H C P N => [K, Q, S, R, D, A, H, C, P, N]

def cauchyCutComparisonToEventFlow : CauchyCutComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCutComparisonFields x).map cauchyCutComparisonEncodeBHist

def cauchyCutComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCutComparisonEventAtDefault index rest

def cauchyCutComparisonFromEventFlow (ef : EventFlow) : Option CauchyCutComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCutComparisonUp.mk
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 0 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 1 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 2 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 3 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 4 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 5 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 6 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 7 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 8 ef))
      (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEventAtDefault 9 ef)))

private theorem CauchyCutComparisonTasteGate_round_trip :
    ∀ x : CauchyCutComparisonUp,
      cauchyCutComparisonFromEventFlow (cauchyCutComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K Q S R D A H C P N =>
      change
        some
          (CauchyCutComparisonUp.mk
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist K))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist Q))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist S))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist R))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist D))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist A))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist H))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist C))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist P))
            (cauchyCutComparisonDecodeBHist (cauchyCutComparisonEncodeBHist N))) =
          some (CauchyCutComparisonUp.mk K Q S R D A H C P N)
      rw [CauchyCutComparisonTasteGate_decode_encode K,
        CauchyCutComparisonTasteGate_decode_encode Q,
        CauchyCutComparisonTasteGate_decode_encode S,
        CauchyCutComparisonTasteGate_decode_encode R,
        CauchyCutComparisonTasteGate_decode_encode D,
        CauchyCutComparisonTasteGate_decode_encode A,
        CauchyCutComparisonTasteGate_decode_encode H,
        CauchyCutComparisonTasteGate_decode_encode C,
        CauchyCutComparisonTasteGate_decode_encode P,
        CauchyCutComparisonTasteGate_decode_encode N]

private theorem CauchyCutComparisonTasteGate_toEventFlow_injective
    {x y : CauchyCutComparisonUp} :
    cauchyCutComparisonToEventFlow x = cauchyCutComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCutComparisonFromEventFlow (cauchyCutComparisonToEventFlow x) =
        cauchyCutComparisonFromEventFlow (cauchyCutComparisonToEventFlow y) :=
    congrArg cauchyCutComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCutComparisonTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyCutComparisonTasteGate_round_trip y)))

instance cauchyCutComparisonBHistCarrier : BHistCarrier CauchyCutComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCutComparisonToEventFlow
  fromEventFlow := cauchyCutComparisonFromEventFlow

instance cauchyCutComparisonChapterTasteGate : ChapterTasteGate CauchyCutComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCutComparisonFromEventFlow (cauchyCutComparisonToEventFlow x) = some x
    exact CauchyCutComparisonTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCutComparisonTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCutComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCutComparisonChapterTasteGate

theorem CauchyCutComparisonRoute [AskSetup] [PackageSetup]
    {K Q S R D A H C P N comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCutComparisonCarrier K Q S R D A H C P N bundle pkg →
      Cont A C comparisonRead →
        PkgSig bundle comparisonRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row K ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                  hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row comparisonRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle comparisonRead pkg ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory comparisonRead ∧ Cont K Q S ∧ Cont S R D ∧ Cont D H A ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sealReplayRead comparisonPkg
  obtain ⟨cutUnary, setoidUnary, readbackUnary, transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, cutSetoidWindow, windowReadbackDyadic,
    dyadicTransportSeal, provenancePkg, localNamePkg⟩ := carrier
  have windowUnary : UnaryHistory S :=
    unary_cont_closed cutUnary setoidUnary cutSetoidWindow
  have dyadicUnary : UnaryHistory D :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadic
  have sealUnary : UnaryHistory A :=
    unary_cont_closed dyadicUnary transportUnary dyadicTransportSeal
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed sealUnary replayUnary sealReplayRead
  have sourceComparison :
      (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row) comparisonRead := by
    exact ⟨hsame_refl comparisonRead, comparisonUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle comparisonRead pkg ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead sourceComparison
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, comparisonPkg, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, comparisonUnary, cutSetoidWindow, windowReadbackDyadic, dyadicTransportSeal,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyCutComparisonUp
