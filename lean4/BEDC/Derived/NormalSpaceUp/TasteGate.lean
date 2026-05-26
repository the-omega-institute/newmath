import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalSpaceUp

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

inductive NormalSpaceUp : Type where
  | mk (T F0 F1 D U0 U1 H K P L : BHist) : NormalSpaceUp
  deriving DecidableEq

def normalSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalSpaceEncodeBHist h

def normalSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalSpaceDecodeBHist tail)

private theorem NormalSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, normalSpaceDecodeBHist (normalSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normalSpaceFields : NormalSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalSpaceUp.mk T F0 F1 D U0 U1 H K P L => [T, F0, F1, D, U0, U1, H, K, P, L]

def normalSpaceToEventFlow : NormalSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (normalSpaceFields x).map normalSpaceEncodeBHist

private def normalSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normalSpaceEventAt index rest

def normalSpaceFromEventFlow (ef : EventFlow) : Option NormalSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NormalSpaceUp.mk
      (normalSpaceDecodeBHist (normalSpaceEventAt 0 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 1 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 2 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 3 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 4 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 5 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 6 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 7 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 8 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 9 ef)))

private theorem NormalSpaceTasteGate_single_carrier_alignment_round_trip
    (x : NormalSpaceUp) :
    normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T F0 F1 D U0 U1 H K P L =>
      change
        some
          (NormalSpaceUp.mk
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist T))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist F0))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist F1))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist D))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist U0))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist U1))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist H))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist K))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist P))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist L))) =
          some (NormalSpaceUp.mk T F0 F1 D U0 U1 H K P L)
      rw [NormalSpaceTasteGate_single_carrier_alignment_decode_encode T,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode F0,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode F1,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode D,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode U0,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode U1,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode H,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode K,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode P,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode L]

private theorem NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NormalSpaceUp} :
    normalSpaceToEventFlow x = normalSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalSpaceFromEventFlow (normalSpaceToEventFlow x) =
        normalSpaceFromEventFlow (normalSpaceToEventFlow y) :=
    congrArg normalSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NormalSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NormalSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance normalSpaceBHistCarrier : BHistCarrier NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalSpaceToEventFlow
  fromEventFlow := normalSpaceFromEventFlow

instance normalSpaceChapterTasteGate : ChapterTasteGate NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x
    exact NormalSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NormalSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, normalSpaceDecodeBHist (normalSpaceEncodeBHist h) = h) ∧
      (∀ x : NormalSpaceUp, normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x) ∧
        (∀ x y : NormalSpaceUp, normalSpaceToEventFlow x = normalSpaceToEventFlow y → x = y) ∧
          normalSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NormalSpaceTasteGate_single_carrier_alignment_decode_encode,
      NormalSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

def NormalSpacePacket [AskSetup] [PackageSetup]
    (topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory topology ∧ UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧
    UnaryHistory disjoint ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ UnaryHistory exported ∧
          Cont closedLeft closedRight disjoint ∧ Cont openLeft openRight transport ∧
            Cont transport replay provenance ∧ Cont provenance localName exported ∧
              PkgSig bundle localName pkg

theorem NormalSpacePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight
            transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight
            transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight
            transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨packet, hsame_refl localName⟩
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
        intro row other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NormalSpacePacket_open_separation_route [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported separationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont disjoint transport separationRead →
        PkgSig bundle exported pkg →
          UnaryHistory topology ∧ UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧
            UnaryHistory disjoint ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
              UnaryHistory separationRead ∧ Cont closedLeft closedRight disjoint ∧
                Cont openLeft openRight transport ∧ Cont disjoint transport separationRead ∧
                  Cont provenance localName exported ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet separationRoute exportedPkg
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed packet.right.right.right.left
      packet.right.right.right.right.right.right.left separationRoute
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.left,
      packet.right.right.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      separationUnary,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left,
      separationRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      exportedPkg⟩

theorem NormalSpacePacket_closed_pair_transport [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported closedLeft' closedRight' disjoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      hsame closedLeft closedLeft' →
        hsame closedRight closedRight' →
          hsame disjoint disjoint' →
            UnaryHistory closedLeft' ∧ UnaryHistory closedRight' ∧ UnaryHistory disjoint' ∧
              Cont closedLeft closedRight disjoint ∧ Cont openLeft openRight transport ∧
                PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameClosedLeft sameClosedRight sameDisjoint
  have closedLeftUnary : UnaryHistory closedLeft' :=
    unary_transport packet.right.left sameClosedLeft
  have closedRightUnary : UnaryHistory closedRight' :=
    unary_transport packet.right.right.left sameClosedRight
  have disjointUnary : UnaryHistory disjoint' :=
    unary_transport packet.right.right.right.left sameDisjoint
  exact
    ⟨closedLeftUnary,
      closedRightUnary,
      disjointUnary,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem NormalSpacePacket_closed_pair_stability [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported transportedClosedLeft transportedClosedRight transportedDisjoint
      replayedName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      hsame closedLeft transportedClosedLeft →
        hsame closedRight transportedClosedRight →
          hsame disjoint transportedDisjoint →
            Cont transportedDisjoint replay replayedName →
              PkgSig bundle replayedName pkg →
                UnaryHistory topology ∧ UnaryHistory transportedClosedLeft ∧
                  UnaryHistory transportedClosedRight ∧ UnaryHistory transportedDisjoint ∧
                    UnaryHistory replayedName ∧ Cont closedLeft closedRight disjoint ∧
                      Cont transportedDisjoint replay replayedName ∧
                        Cont provenance localName exported ∧ PkgSig bundle localName pkg ∧
                          PkgSig bundle replayedName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameClosedLeft sameClosedRight sameDisjoint replayRoute replayPkg
  have transported :
      UnaryHistory transportedClosedLeft ∧ UnaryHistory transportedClosedRight ∧
        UnaryHistory transportedDisjoint ∧ Cont closedLeft closedRight disjoint ∧
          Cont openLeft openRight transport ∧ PkgSig bundle localName pkg :=
    NormalSpacePacket_closed_pair_transport packet sameClosedLeft sameClosedRight sameDisjoint
  have replayedUnary : UnaryHistory replayedName :=
    unary_cont_closed transported.right.right.left
      packet.right.right.right.right.right.right.right.left replayRoute
  exact
    ⟨packet.left,
      transported.left,
      transported.right.left,
      transported.right.right.left,
      replayedUnary,
      transported.right.right.right.left,
      replayRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      transported.right.right.right.right.right,
      replayPkg⟩

theorem NormalSpacePacket_open_neighborhood_stability [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported openLeft' openRight' stabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg ->
      hsame openLeft openLeft' -> hsame openRight openRight' ->
        Cont openLeft' openRight' stabilityRead ->
          UnaryHistory openLeft' ∧ UnaryHistory openRight' ∧ UnaryHistory stabilityRead ∧
            Cont openLeft' openRight' stabilityRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameOpenLeft sameOpenRight stabilityRoute
  have openLeftUnary : UnaryHistory openLeft' :=
    unary_transport packet.right.right.right.right.left sameOpenLeft
  have openRightUnary : UnaryHistory openRight' :=
    unary_transport packet.right.right.right.right.right.left sameOpenRight
  have stabilityUnary : UnaryHistory stabilityRead :=
    unary_cont_closed openLeftUnary openRightUnary stabilityRoute
  exact
    ⟨openLeftUnary,
      openRightUnary,
      stabilityUnary,
      stabilityRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem NormalSpacePacket_cozero_urysohn_handoff [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported handoff consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont openLeft openRight handoff →
        Cont handoff replay consumer →
          PkgSig bundle exported pkg →
            UnaryHistory handoff ∧ UnaryHistory consumer ∧ Cont openLeft openRight handoff ∧
              Cont handoff replay consumer ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet openHandoff consumerRoute exportedPkg
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.left openHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary packet.right.right.right.right.right.right.right.left
      consumerRoute
  exact
    ⟨handoffUnary,
      consumerUnary,
      openHandoff,
      consumerRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      exportedPkg⟩

end BEDC.Derived.NormalSpaceUp
