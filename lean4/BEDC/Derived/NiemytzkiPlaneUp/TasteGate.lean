import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NiemytzkiPlaneUp

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

theorem NiemytzkiPlaneNameCertObligations [AskSetup] [PackageSetup]
    {upper boundary tangent coordinate classifier transport replay provenance localName
      namedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory upper ->
      UnaryHistory boundary ->
        UnaryHistory tangent ->
          UnaryHistory coordinate ->
            UnaryHistory classifier ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  UnaryHistory provenance ->
                    UnaryHistory localName ->
                      Cont boundary tangent coordinate ->
                        Cont classifier replay namedRoute ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row upper ∨ hsame row boundary ∨
                                      hsame row tangent ∨ hsame row coordinate ∨
                                        hsame row classifier ∨ hsame row transport ∨
                                          hsame row replay ∨ hsame row provenance ∨
                                            hsame row localName ∨ hsame row namedRoute)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont boundary tangent coordinate ∧
                                      Cont classifier replay namedRoute ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory namedRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _upperUnary boundaryUnary tangentUnary _coordinateUnary classifierUnary
    _transportUnary replayUnary provenanceUnary _localNameUnary boundaryTangentCoordinate
    classifierReplayNamed provenancePkg localNamePkg
  have coordinateUnary : UnaryHistory coordinate :=
    unary_cont_closed boundaryUnary tangentUnary boundaryTangentCoordinate
  have namedRouteUnary : UnaryHistory namedRoute :=
    unary_cont_closed classifierUnary replayUnary classifierReplayNamed
  have sourceNamed : hsame namedRoute namedRoute ∧ UnaryHistory namedRoute :=
    ⟨hsame_refl namedRoute, namedRouteUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row upper ∨ hsame row boundary ∨ hsame row tangent ∨
              hsame row coordinate ∨ hsame row classifier ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row namedRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundary tangent coordinate ∧
              Cont classifier replay namedRoute ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRoute sourceNamed
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryTangentCoordinate, classifierReplayNamed, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, namedRouteUnary⟩

inductive NiemytzkiPlaneUp : Type where
  | mk (U B T R Q H C P L : BHist) : NiemytzkiPlaneUp
  deriving DecidableEq

def niemytzkiPlaneEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: niemytzkiPlaneEncodeBHist h
  | BHist.e1 h => BMark.b1 :: niemytzkiPlaneEncodeBHist h

def niemytzkiPlaneDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (niemytzkiPlaneDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (niemytzkiPlaneDecodeBHist tail)

private theorem NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def niemytzkiPlaneFields : NiemytzkiPlaneUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NiemytzkiPlaneUp.mk U B T R Q H C P L => [U, B, T, R, Q, H, C, P, L]

def niemytzkiPlaneToEventFlow : NiemytzkiPlaneUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (niemytzkiPlaneFields x).map niemytzkiPlaneEncodeBHist

private def niemytzkiPlaneEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => niemytzkiPlaneEventAt index rest

def niemytzkiPlaneFromEventFlow (ef : EventFlow) : Option NiemytzkiPlaneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NiemytzkiPlaneUp.mk
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 0 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 1 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 2 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 3 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 4 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 5 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 6 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 7 ef))
      (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEventAt 8 ef)))

private theorem NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip
    (x : NiemytzkiPlaneUp) :
    niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U B T R Q H C P L =>
      change
        some
          (NiemytzkiPlaneUp.mk
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist U))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist B))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist T))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist R))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist Q))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist H))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist C))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist P))
            (niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist L))) =
          some (NiemytzkiPlaneUp.mk U B T R Q H C P L)
      rw [NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode U,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode B,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode T,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode R,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode Q,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode H,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode C,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode P,
        NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode L]

private theorem NiemytzkiPlaneToEventFlow_injective {x y : NiemytzkiPlaneUp} :
    niemytzkiPlaneToEventFlow x = niemytzkiPlaneToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow x) =
        niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow y) :=
    congrArg niemytzkiPlaneFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip y)))

instance niemytzkiPlaneBHistCarrier : BHistCarrier NiemytzkiPlaneUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := niemytzkiPlaneToEventFlow
  fromEventFlow := niemytzkiPlaneFromEventFlow

instance niemytzkiPlaneChapterTasteGate : ChapterTasteGate NiemytzkiPlaneUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change niemytzkiPlaneFromEventFlow (niemytzkiPlaneToEventFlow x) = some x
    exact NiemytzkiPlaneTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NiemytzkiPlaneToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NiemytzkiPlaneUp :=
  -- BEDC touchpoint anchor: BHist BMark
  niemytzkiPlaneChapterTasteGate

theorem NiemytzkiPlaneTasteGate_single_carrier_alignment :
    (forall h : BHist, niemytzkiPlaneDecodeBHist (niemytzkiPlaneEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NiemytzkiPlaneUp) ∧
        Nonempty (ChapterTasteGate NiemytzkiPlaneUp) ∧
          niemytzkiPlaneEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NiemytzkiPlaneTasteGate_single_carrier_alignment_decode_encode,
      ⟨niemytzkiPlaneBHistCarrier⟩,
      ⟨niemytzkiPlaneChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.NiemytzkiPlaneUp
