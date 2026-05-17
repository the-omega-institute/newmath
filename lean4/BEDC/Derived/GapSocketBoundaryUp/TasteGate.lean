import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GapSocketBoundaryUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GapSocketBoundaryUp : Type where
  | packet :
      (typedSocket externalityGate apophaticFarEnd refusalLedger transport route provenance
        localName : BHist) → GapSocketBoundaryUp

def gapSocketBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gapSocketBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gapSocketBoundaryEncodeBHist h

def gapSocketBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gapSocketBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gapSocketBoundaryDecodeBHist tail)

private theorem gapSocketBoundaryDecodeEncodeBHist :
    ∀ h : BHist, gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def GapSocketBoundaryCarrier :
    GapSocketBoundaryUp → Prop
  -- BEDC touchpoint anchor: BHist BMark
  | GapSocketBoundaryUp.packet typedSocket externalityGate apophaticFarEnd refusalLedger
      transport route provenance localName =>
      UnaryHistory typedSocket ∧ UnaryHistory externalityGate ∧
        UnaryHistory apophaticFarEnd ∧ UnaryHistory refusalLedger ∧
          UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
            UnaryHistory localName

def gapSocketBoundaryFields : GapSocketBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GapSocketBoundaryUp.packet typedSocket externalityGate apophaticFarEnd refusalLedger
      transport route provenance localName =>
      [typedSocket, externalityGate, apophaticFarEnd, refusalLedger, transport, route,
        provenance, localName]

def gapSocketBoundaryToEventFlow : GapSocketBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gapSocketBoundaryFields x).map gapSocketBoundaryEncodeBHist

def gapSocketBoundaryFromEventFlow : EventFlow → Option GapSocketBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | typedSocket :: rest0 =>
      match rest0 with
      | [] => none
      | externalityGate :: rest1 =>
          match rest1 with
          | [] => none
          | apophaticFarEnd :: rest2 =>
              match rest2 with
              | [] => none
              | refusalLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (GapSocketBoundaryUp.packet
                                          (gapSocketBoundaryDecodeBHist typedSocket)
                                          (gapSocketBoundaryDecodeBHist externalityGate)
                                          (gapSocketBoundaryDecodeBHist apophaticFarEnd)
                                          (gapSocketBoundaryDecodeBHist refusalLedger)
                                          (gapSocketBoundaryDecodeBHist transport)
                                          (gapSocketBoundaryDecodeBHist route)
                                          (gapSocketBoundaryDecodeBHist provenance)
                                          (gapSocketBoundaryDecodeBHist localName))
                                  | _ :: _ => none

private theorem gapSocketBoundary_round_trip :
    ∀ x : GapSocketBoundaryUp,
      gapSocketBoundaryFromEventFlow (gapSocketBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet typedSocket externalityGate apophaticFarEnd refusalLedger transport route provenance
      localName =>
      change
        some
            (GapSocketBoundaryUp.packet
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist typedSocket))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist externalityGate))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist apophaticFarEnd))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist refusalLedger))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist transport))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist route))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist provenance))
              (gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist localName))) =
          some
            (GapSocketBoundaryUp.packet typedSocket externalityGate apophaticFarEnd
              refusalLedger transport route provenance localName)
      rw [gapSocketBoundaryDecodeEncodeBHist typedSocket,
        gapSocketBoundaryDecodeEncodeBHist externalityGate,
        gapSocketBoundaryDecodeEncodeBHist apophaticFarEnd,
        gapSocketBoundaryDecodeEncodeBHist refusalLedger,
        gapSocketBoundaryDecodeEncodeBHist transport,
        gapSocketBoundaryDecodeEncodeBHist route,
        gapSocketBoundaryDecodeEncodeBHist provenance,
        gapSocketBoundaryDecodeEncodeBHist localName]

private theorem gapSocketBoundaryToEventFlow_injective {x y : GapSocketBoundaryUp} :
    gapSocketBoundaryToEventFlow x = gapSocketBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gapSocketBoundaryFromEventFlow (gapSocketBoundaryToEventFlow x) =
        gapSocketBoundaryFromEventFlow (gapSocketBoundaryToEventFlow y) :=
    congrArg gapSocketBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (gapSocketBoundary_round_trip x).symm
      (Eq.trans hread (gapSocketBoundary_round_trip y)))

private theorem gapSocketBoundaryFieldsFaithful :
    ∀ x y : GapSocketBoundaryUp, gapSocketBoundaryFields x = gapSocketBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet typedSocket externalityGate apophaticFarEnd refusalLedger transport route
      provenance localName =>
      cases y with
      | packet typedSocket' externalityGate' apophaticFarEnd' refusalLedger' transport'
          route' provenance' localName' =>
          cases hfields
          rfl

instance gapSocketBoundaryBHistCarrier : BHistCarrier GapSocketBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gapSocketBoundaryToEventFlow
  fromEventFlow := gapSocketBoundaryFromEventFlow

instance gapSocketBoundaryChapterTasteGate : ChapterTasteGate GapSocketBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gapSocketBoundaryFromEventFlow (gapSocketBoundaryToEventFlow x) = some x
    exact gapSocketBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gapSocketBoundaryToEventFlow_injective heq)

instance gapSocketBoundaryFieldFaithful : FieldFaithful GapSocketBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gapSocketBoundaryFields
  field_faithful := gapSocketBoundaryFieldsFaithful

instance gapSocketBoundaryNontrivial : Nontrivial GapSocketBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GapSocketBoundaryUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      GapSocketBoundaryUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GapSocketBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gapSocketBoundaryChapterTasteGate

theorem GapSocketBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {typedSocket externalityGate apophaticFarEnd refusalLedger transport route provenance
      localName typedReplay gateReplay farEndReplay refusalReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GapSocketBoundaryCarrier
        (GapSocketBoundaryUp.packet typedSocket externalityGate apophaticFarEnd refusalLedger
          transport route provenance localName) ->
      Cont typedSocket externalityGate typedReplay ->
        Cont externalityGate apophaticFarEnd gateReplay ->
          Cont apophaticFarEnd refusalLedger farEndReplay ->
            Cont refusalLedger localName refusalReplay ->
              PkgSig bundle provenance pkg ->
                UnaryHistory typedSocket ∧ UnaryHistory externalityGate ∧
                  UnaryHistory apophaticFarEnd ∧ UnaryHistory refusalLedger ∧
                    UnaryHistory typedReplay ∧ UnaryHistory gateReplay ∧
                      UnaryHistory farEndReplay ∧ UnaryHistory refusalReplay ∧
                        Cont typedSocket externalityGate typedReplay ∧
                          Cont externalityGate apophaticFarEnd gateReplay ∧
                            Cont apophaticFarEnd refusalLedger farEndReplay ∧
                              Cont refusalLedger localName refusalReplay ∧
                                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier typedCont gateCont farEndCont refusalCont provenancePkg
  obtain ⟨typedUnary, gateUnary, farEndUnary, refusalUnary, _transportUnary, _routeUnary,
    _provenanceUnary, localNameUnary⟩ := carrier
  have typedReplayUnary : UnaryHistory typedReplay :=
    unary_cont_closed typedUnary gateUnary typedCont
  have gateReplayUnary : UnaryHistory gateReplay :=
    unary_cont_closed gateUnary farEndUnary gateCont
  have farEndReplayUnary : UnaryHistory farEndReplay :=
    unary_cont_closed farEndUnary refusalUnary farEndCont
  have refusalReplayUnary : UnaryHistory refusalReplay :=
    unary_cont_closed refusalUnary localNameUnary refusalCont
  exact
    ⟨typedUnary, gateUnary, farEndUnary, refusalUnary, typedReplayUnary, gateReplayUnary,
      farEndReplayUnary, refusalReplayUnary, typedCont, gateCont, farEndCont, refusalCont,
      provenancePkg⟩

theorem GapSocketBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, gapSocketBoundaryDecodeBHist (gapSocketBoundaryEncodeBHist h) = h) ∧
      (∀ x : GapSocketBoundaryUp,
        gapSocketBoundaryFromEventFlow (gapSocketBoundaryToEventFlow x) = some x) ∧
        (∀ x y : GapSocketBoundaryUp, gapSocketBoundaryToEventFlow x =
          gapSocketBoundaryToEventFlow y → x = y) ∧
          gapSocketBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨gapSocketBoundaryDecodeEncodeBHist, gapSocketBoundary_round_trip,
    fun _ _ heq => gapSocketBoundaryToEventFlow_injective heq, rfl⟩

end BEDC.Derived.GapSocketBoundaryUp
