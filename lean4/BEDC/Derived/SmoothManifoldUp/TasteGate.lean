import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SmoothManifoldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SmoothManifoldUp : Type where
  | mk (B T V A O S R H C P N : BHist) : SmoothManifoldUp
  deriving DecidableEq

def smoothManifoldEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: smoothManifoldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: smoothManifoldEncodeBHist h

def smoothManifoldDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (smoothManifoldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (smoothManifoldDecodeBHist tail)

private theorem SmoothManifoldTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, smoothManifoldDecodeBHist (smoothManifoldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def smoothManifoldToEventFlow : SmoothManifoldUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SmoothManifoldUp.mk B T V A O S R H C P N =>
      [smoothManifoldEncodeBHist B,
        smoothManifoldEncodeBHist T,
        smoothManifoldEncodeBHist V,
        smoothManifoldEncodeBHist A,
        smoothManifoldEncodeBHist O,
        smoothManifoldEncodeBHist S,
        smoothManifoldEncodeBHist R,
        smoothManifoldEncodeBHist H,
        smoothManifoldEncodeBHist C,
        smoothManifoldEncodeBHist P,
        smoothManifoldEncodeBHist N]

private def smoothManifoldEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => smoothManifoldEventAt index rest

def smoothManifoldDecodeFields (ef : EventFlow) : SmoothManifoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SmoothManifoldUp.mk
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 0 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 1 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 2 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 3 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 4 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 5 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 6 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 7 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 8 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 9 ef))
    (smoothManifoldDecodeBHist (smoothManifoldEventAt 10 ef))

def smoothManifoldFromEventFlow : EventFlow -> Option SmoothManifoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef => some (smoothManifoldDecodeFields ef)

private theorem SmoothManifoldTasteGate_single_carrier_alignment_round_trip
    (x : SmoothManifoldUp) :
    smoothManifoldFromEventFlow (smoothManifoldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B T V A O S R H C P N =>
      change
        some
            (SmoothManifoldUp.mk
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist B))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist T))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist V))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist A))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist O))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist S))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist R))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist H))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist C))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist P))
              (smoothManifoldDecodeBHist (smoothManifoldEncodeBHist N))) =
          some (SmoothManifoldUp.mk B T V A O S R H C P N)
      rw [SmoothManifoldTasteGate_single_carrier_alignment_decode_encode B,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode T,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode V,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode A,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode O,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode S,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode R,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode H,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode C,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode P,
        SmoothManifoldTasteGate_single_carrier_alignment_decode_encode N]

private theorem SmoothManifoldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SmoothManifoldUp} :
    smoothManifoldToEventFlow x = smoothManifoldToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      smoothManifoldFromEventFlow (smoothManifoldToEventFlow x) =
        smoothManifoldFromEventFlow (smoothManifoldToEventFlow y) :=
    congrArg smoothManifoldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SmoothManifoldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SmoothManifoldTasteGate_single_carrier_alignment_round_trip y)))

instance smoothManifoldBHistCarrier : BHistCarrier SmoothManifoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := smoothManifoldToEventFlow
  fromEventFlow := smoothManifoldFromEventFlow

instance smoothManifoldChapterTasteGate : ChapterTasteGate SmoothManifoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change smoothManifoldFromEventFlow (smoothManifoldToEventFlow x) = some x
    exact SmoothManifoldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SmoothManifoldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SmoothManifoldTasteGate_single_carrier_alignment :
    (forall h : BHist, smoothManifoldDecodeBHist (smoothManifoldEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SmoothManifoldUp) ∧
        Nonempty (ChapterTasteGate SmoothManifoldUp) ∧
          smoothManifoldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SmoothManifoldTasteGate_single_carrier_alignment_decode_encode,
      ⟨smoothManifoldBHistCarrier⟩,
      ⟨smoothManifoldChapterTasteGate⟩,
      rfl⟩

def SmoothManifoldCarrier [AskSetup] [PackageSetup]
    (base topology model atlas overlap transition readiness transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory base ∧ UnaryHistory topology ∧ UnaryHistory model ∧ UnaryHistory atlas ∧
    UnaryHistory overlap ∧ UnaryHistory transition ∧ UnaryHistory readiness ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg

theorem SmoothManifoldNamecertObligations [AskSetup] [PackageSetup]
    {base topology model atlas overlap transition readiness transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SmoothManifoldCarrier base topology model atlas overlap transition readiness transport
        replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row base ∨ hsame row topology ∨ hsame row model ∨ hsame row atlas ∨
              hsame row overlap ∨ hsame row transition ∨ hsame row readiness)
          (fun row : BHist => hsame row readiness ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory base ∧ UnaryHistory topology ∧ UnaryHistory model ∧ UnaryHistory atlas ∧
          UnaryHistory overlap ∧ UnaryHistory transition ∧ UnaryHistory readiness ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨baseUnary, topologyUnary, modelUnary, atlasUnary, overlapUnary, transitionUnary,
    readinessUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg⟩ := carrier
  have sourceReadiness :
      (fun row : BHist => hsame row readiness ∧ UnaryHistory row) readiness := by
    exact ⟨hsame_refl readiness, readinessUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row base ∨ hsame row topology ∨ hsame row model ∨ hsame row atlas ∨
              hsame row overlap ∨ hsame row transition ∨ hsame row readiness)
          (fun row : BHist => hsame row readiness ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readiness sourceReadiness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, baseUnary, topologyUnary, modelUnary, atlasUnary, overlapUnary, transitionUnary,
      readinessUnary, provenancePkg⟩

end BEDC.Derived.SmoothManifoldUp
