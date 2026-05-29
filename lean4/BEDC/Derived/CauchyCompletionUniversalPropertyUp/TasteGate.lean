import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUniversalPropertyUp

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

inductive CauchyCompletionUniversalPropertyUp : Type where
  | mk (D K T F E L H C P N : BHist) :
      CauchyCompletionUniversalPropertyUp
  deriving DecidableEq

def cauchyCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUniversalPropertyEncodeBHist h

def cauchyCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUniversalPropertyDecodeBHist tail)

private theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionUniversalPropertyFields :
    CauchyCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N =>
      [D, K, T, F, E, L, H, C, P, N]

def cauchyCompletionUniversalPropertyToEventFlow :
    CauchyCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionUniversalPropertyFields x).map
      cauchyCompletionUniversalPropertyEncodeBHist

private def cauchyCompletionUniversalPropertyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionUniversalPropertyEventAtDefault index rest

def cauchyCompletionUniversalPropertyFromEventFlow :
    EventFlow → Option CauchyCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionUniversalPropertyUp.mk
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 0 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 1 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 2 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 3 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 4 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 5 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 6 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 7 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 8 ef))
        (cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEventAtDefault 9 ef)))

private theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionUniversalPropertyUp,
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D K T F E L H C P N =>
      change
        some
            (CauchyCompletionUniversalPropertyUp.mk
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist D))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist K))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist T))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist F))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist E))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist L))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist H))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist C))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist P))
              (cauchyCompletionUniversalPropertyDecodeBHist
                (cauchyCompletionUniversalPropertyEncodeBHist N))) =
          some (CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N)
      rw [CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode K,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode F,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode L,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionUniversalPropertyUp} :
    cauchyCompletionUniversalPropertyToEventFlow x =
        cauchyCompletionUniversalPropertyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow y) :=
    congrArg cauchyCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionUniversalPropertyBHistCarrier :
    BHistCarrier CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUniversalPropertyToEventFlow
  fromEventFlow := cauchyCompletionUniversalPropertyFromEventFlow

instance cauchyCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        some x
    exact CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ D K T F E L H C P N : BHist,
        cauchyCompletionUniversalPropertyFields
          (CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N) =
            [D, K, T, F, E, L, H, C, P, N]) ∧
      cauchyCompletionUniversalPropertyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro D K T F E L H C P N
    rfl
  · rfl

def CauchyCompletionUniversalPropertyCarrier [AskSetup] [PackageSetup]
    (D K T F E L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory K ∧ UnaryHistory T ∧ UnaryHistory F ∧
    UnaryHistory E ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCompletionUniversalPropertyCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {D K T F E L H C P N denseRead extensionRead uniquenessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUniversalPropertyCarrier D K T F E L H C P N bundle pkg ->
      Cont D F denseRead ->
        Cont K T extensionRead ->
          Cont E L uniquenessRead ->
            PkgSig bundle uniquenessRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row uniquenessRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row K ∨ hsame row T ∨ hsame row F ∨
                      hsame row E ∨ hsame row L ∨ hsame row uniquenessRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D F denseRead ∧ Cont K T extensionRead ∧
                      Cont E L uniquenessRead ∧ PkgSig bundle uniquenessRead pkg)
                  hsame ∧
                UnaryHistory denseRead ∧ UnaryHistory extensionRead ∧
                  UnaryHistory uniquenessRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier denseRoute extensionRoute uniquenessRoute uniquenessPkg
  obtain ⟨DUnary, KUnary, TUnary, FUnary, EUnary, LUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _provenancePkg, _localPkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed DUnary FUnary denseRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed KUnary TUnary extensionRoute
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed EUnary LUnary uniquenessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniquenessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row K ∨ hsame row T ∨ hsame row F ∨
              hsame row E ∨ hsame row L ∨ hsame row uniquenessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D F denseRead ∧ Cont K T extensionRead ∧
              Cont E L uniquenessRead ∧ PkgSig bundle uniquenessRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniquenessRead ⟨hsame_refl uniquenessRead, uniquenessUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, denseRoute, extensionRoute, uniquenessRoute, uniquenessPkg⟩
  }
  exact ⟨cert, denseUnary, extensionUnary, uniquenessUnary⟩

end BEDC.Derived.CauchyCompletionUniversalPropertyUp
