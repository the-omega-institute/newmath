import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffSpaceUp

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

inductive HausdorffSpaceUp : Type where
  | mk (T x y U V D M E H C P N : BHist) : HausdorffSpaceUp
  deriving DecidableEq

def hausdorffSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffSpaceEncodeBHist h

def hausdorffSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffSpaceDecodeBHist tail)

private theorem HausdorffSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffSpaceFields : HausdorffSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffSpaceUp.mk T x y U V D M E H C P N => [T, x, y, U, V, D, M, E, H, C, P, N]

def hausdorffSpaceToEventFlow : HausdorffSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hausdorffSpaceFields x).map hausdorffSpaceEncodeBHist

private def hausdorffSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffSpaceEventAtDefault index rest

def hausdorffSpaceFromEventFlow (ef : EventFlow) : Option HausdorffSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffSpaceUp.mk
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 0 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 1 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 2 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 3 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 4 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 5 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 6 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 7 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 8 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 9 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 10 ef))
      (hausdorffSpaceDecodeBHist (hausdorffSpaceEventAtDefault 11 ef)))

private theorem HausdorffSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffSpaceUp,
      hausdorffSpaceFromEventFlow (hausdorffSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk T x y U V D M E H C P N =>
      change
        some
          (HausdorffSpaceUp.mk
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist T))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist x))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist y))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist U))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist V))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist D))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist M))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist E))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist H))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist C))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist P))
            (hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist N))) =
          some (HausdorffSpaceUp.mk T x y U V D M E H C P N)
      rw [HausdorffSpaceTasteGate_single_carrier_alignment_decode T,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode x,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode y,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode U,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode V,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode D,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode M,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode E,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode H,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode C,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode P,
        HausdorffSpaceTasteGate_single_carrier_alignment_decode N]

private theorem HausdorffSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffSpaceUp} :
    hausdorffSpaceToEventFlow x = hausdorffSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffSpaceFromEventFlow (hausdorffSpaceToEventFlow x) =
        hausdorffSpaceFromEventFlow (hausdorffSpaceToEventFlow y) :=
    congrArg hausdorffSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HausdorffSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance hausdorffSpaceBHistCarrier : BHistCarrier HausdorffSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffSpaceToEventFlow
  fromEventFlow := hausdorffSpaceFromEventFlow

instance hausdorffSpaceChapterTasteGate : ChapterTasteGate HausdorffSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffSpaceFromEventFlow (hausdorffSpaceToEventFlow x) = some x
    exact HausdorffSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hausdorffSpaceFieldFaithful : FieldFaithful HausdorffSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffSpaceFields
  field_faithful := by
    intro x y h
    exact HausdorffSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
      (congrArg (List.map hausdorffSpaceEncodeBHist) h)

instance hausdorffSpaceNontrivial : Nontrivial HausdorffSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffSpaceChapterTasteGate

theorem HausdorffSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, hausdorffSpaceDecodeBHist (hausdorffSpaceEncodeBHist h) = h) ∧
      (∀ x : HausdorffSpaceUp,
        hausdorffSpaceFromEventFlow (hausdorffSpaceToEventFlow x) = some x) ∧
        (∀ x y : HausdorffSpaceUp,
          hausdorffSpaceToEventFlow x = hausdorffSpaceToEventFlow y -> x = y) ∧
          hausdorffSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HausdorffSpaceTasteGate_single_carrier_alignment_decode,
      HausdorffSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HausdorffSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

def HausdorffSpaceCarrier [AskSetup] [PackageSetup]
    (T x y U V D M E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory T ∧ UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory U ∧
    UnaryHistory V ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont T x H ∧ Cont H y C ∧ Cont U V D ∧ Cont M E C ∧
          PkgSig bundle P pkg

theorem HausdorffSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N (And.intro carrier (hsame_refl N))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem HausdorffSpaceCarrier_metric_separation_handoff [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N metricReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      Cont M E metricReplay ->
        UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory U ∧ UnaryHistory V ∧
          UnaryHistory D ∧ UnaryHistory metricReplay ∧ Cont M E metricReplay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier metricRoute
  exact
    ⟨carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      unary_cont_closed
        carrier.right.right.right.right.right.right.left
        carrier.right.right.right.right.right.right.right.left
        metricRoute,
      metricRoute⟩

theorem HausdorffSpaceCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N metricRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      Cont M E metricRead ->
        Cont metricRead D realRead ->
          UnaryHistory T ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
            UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory metricRead ∧
              UnaryHistory realRead ∧ Cont M E metricRead ∧
                Cont metricRead D realRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier metricRoute realRoute
  obtain ⟨tUnary, _xUnary, _yUnary, uUnary, vUnary, dUnary, mUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _pointRoute, _pointClassifier, _separationRoute,
    _metricCarrierRoute, pkgRow⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed mUnary eUnary metricRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary dUnary realRoute
  exact
    ⟨tUnary, uUnary, vUnary, dUnary, mUnary, eUnary, metricReadUnary, realReadUnary,
      metricRoute, realRoute, pkgRow⟩

theorem HausdorffSpaceNameCert_obligations
    {T x y U V D M E H C P N separation metricRoute realSealRoute : BHist}
    (openRoute : Cont T U C) (disjointRoute : Cont V D separation)
    (metricHandoff : Cont M E metricRoute)
    (sealHandoff : Cont metricRoute separation realSealRoute) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row T ∧
          ∃ packet : HausdorffSpaceUp,
            packet = HausdorffSpaceUp.mk T x y U V D M E H C P N)
      (fun row : BHist =>
        Cont T U C ∧ Cont V D separation ∧ hsame row T ∧ hsame U U ∧ hsame V V ∧
          hsame D D)
      (fun row : BHist =>
        Cont M E metricRoute ∧ Cont metricRoute separation realSealRoute ∧ hsame row T ∧
          hsame P P ∧ hsame N N)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro T
          ⟨hsame_refl T,
            Exists.intro (HausdorffSpaceUp.mk T x y U V D M E H C P N) rfl⟩
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
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨openRoute, disjointRoute, source.left, hsame_refl U, hsame_refl V, hsame_refl D⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨metricHandoff, sealHandoff, source.left, hsame_refl P, hsame_refl N⟩
  }

end BEDC.Derived.HausdorffSpaceUp
