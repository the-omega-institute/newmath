import BEDC.Derived.InitialUniformityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InitialUniformityUp

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

inductive InitialUniformityPullbackEntourageStabilityCarrier : Type where
  | mk (source target map entourage transport replay provenance localName : BHist) :
      InitialUniformityPullbackEntourageStabilityCarrier
  deriving DecidableEq

def InitialUniformityPullbackEntourageStability_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: InitialUniformityPullbackEntourageStability_encodeBHist h
  | BHist.e1 h => BMark.b1 :: InitialUniformityPullbackEntourageStability_encodeBHist h

def InitialUniformityPullbackEntourageStability_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (InitialUniformityPullbackEntourageStability_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (InitialUniformityPullbackEntourageStability_decodeBHist tail)

private theorem InitialUniformityPullbackEntourageStability_decode_encode :
    ∀ h : BHist,
      InitialUniformityPullbackEntourageStability_decodeBHist
          (InitialUniformityPullbackEntourageStability_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def InitialUniformityPullbackEntourageStability_fields :
    InitialUniformityPullbackEntourageStabilityCarrier → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InitialUniformityPullbackEntourageStabilityCarrier.mk source target map entourage
      transport replay provenance localName =>
      [source, target, map, entourage, transport, replay, provenance, localName]

def InitialUniformityPullbackEntourageStability_toEventFlow :
    InitialUniformityPullbackEntourageStabilityCarrier → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (InitialUniformityPullbackEntourageStability_fields x).map
        InitialUniformityPullbackEntourageStability_encodeBHist

private def InitialUniformityPullbackEntourageStability_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      InitialUniformityPullbackEntourageStability_eventAt index rest

def InitialUniformityPullbackEntourageStability_fromEventFlow
    (ef : EventFlow) : Option InitialUniformityPullbackEntourageStabilityCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (InitialUniformityPullbackEntourageStabilityCarrier.mk
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 0 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 1 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 2 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 3 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 4 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 5 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 6 ef))
      (InitialUniformityPullbackEntourageStability_decodeBHist
        (InitialUniformityPullbackEntourageStability_eventAt 7 ef)))

private theorem InitialUniformityPullbackEntourageStability_round_trip
    (x : InitialUniformityPullbackEntourageStabilityCarrier) :
    InitialUniformityPullbackEntourageStability_fromEventFlow
        (InitialUniformityPullbackEntourageStability_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source target map entourage transport replay provenance localName =>
      change
        some
            (InitialUniformityPullbackEntourageStabilityCarrier.mk
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist source))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist target))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist map))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist entourage))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist transport))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist replay))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist provenance))
              (InitialUniformityPullbackEntourageStability_decodeBHist
                (InitialUniformityPullbackEntourageStability_encodeBHist localName))) =
          some
            (InitialUniformityPullbackEntourageStabilityCarrier.mk source target map
              entourage transport replay provenance localName)
      rw [InitialUniformityPullbackEntourageStability_decode_encode source,
        InitialUniformityPullbackEntourageStability_decode_encode target,
        InitialUniformityPullbackEntourageStability_decode_encode map,
        InitialUniformityPullbackEntourageStability_decode_encode entourage,
        InitialUniformityPullbackEntourageStability_decode_encode transport,
        InitialUniformityPullbackEntourageStability_decode_encode replay,
        InitialUniformityPullbackEntourageStability_decode_encode provenance,
        InitialUniformityPullbackEntourageStability_decode_encode localName]

private theorem InitialUniformityPullbackEntourageStability_toEventFlow_injective
    {x y : InitialUniformityPullbackEntourageStabilityCarrier} :
    InitialUniformityPullbackEntourageStability_toEventFlow x =
        InitialUniformityPullbackEntourageStability_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      InitialUniformityPullbackEntourageStability_fromEventFlow
          (InitialUniformityPullbackEntourageStability_toEventFlow x) =
        InitialUniformityPullbackEntourageStability_fromEventFlow
          (InitialUniformityPullbackEntourageStability_toEventFlow y) :=
    congrArg InitialUniformityPullbackEntourageStability_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (InitialUniformityPullbackEntourageStability_round_trip x).symm
      (Eq.trans hread (InitialUniformityPullbackEntourageStability_round_trip y)))

instance InitialUniformityPullbackEntourageStability_BHistCarrier :
    BHistCarrier InitialUniformityPullbackEntourageStabilityCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := InitialUniformityPullbackEntourageStability_toEventFlow
  fromEventFlow := InitialUniformityPullbackEntourageStability_fromEventFlow

instance InitialUniformityPullbackEntourageStability_ChapterTasteGate :
    ChapterTasteGate InitialUniformityPullbackEntourageStabilityCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      InitialUniformityPullbackEntourageStability_fromEventFlow
          (InitialUniformityPullbackEntourageStability_toEventFlow x) =
        some x
    exact InitialUniformityPullbackEntourageStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InitialUniformityPullbackEntourageStability_toEventFlow_injective heq)

theorem InitialUniformityPullbackEntourageStability [AskSetup] [PackageSetup]
    {source target map entourage transport replay provenance localName pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.InitialUniformityUp source target map entourage transport replay provenance
        localName bundle pkg ->
      Cont source map entourage ->
        Cont target entourage replay ->
          Cont entourage replay pullbackRead ->
            PkgSig bundle pullbackRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row pullbackRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row target ∨ hsame row map ∨
                      hsame row entourage ∨ hsame row transport ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row localName ∨ hsame row pullbackRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont source map entourage ∧
                      Cont target entourage replay ∧ Cont entourage replay pullbackRead ∧
                        PkgSig bundle pullbackRead pkg)
                  hsame ∧
                UnaryHistory pullbackRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute targetRoute pullbackRoute pullbackPkg
  obtain ⟨_sourceUnary, _targetUnary, _mapUnary, entourageUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, _carrierSourceRoute, _carrierTargetRoute,
    _provenancePkg, _localNamePkg⟩ := carrier
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed entourageUnary replayUnary pullbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row pullbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row map ∨ hsame row entourage ∨
              hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row pullbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source map entourage ∧ Cont target entourage replay ∧
              Cont entourage replay pullbackRead ∧ PkgSig bundle pullbackRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro pullbackRead
        ⟨hsame_refl pullbackRead, pullbackUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, targetRoute, pullbackRoute, pullbackPkg⟩
  }
  exact ⟨cert, pullbackUnary⟩

end BEDC.Derived.InitialUniformityUp
