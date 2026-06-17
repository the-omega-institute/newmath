import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

/-!
# ReachabilityGramianUp finite carrier.
-/

namespace BEDC.Derived.ReachabilityGramianUp

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

inductive ReachabilityGramianUp : Type where
  | mk
      (transition control horizon gramian transport route provenance cert endpoint : BHist) :
      ReachabilityGramianUp
  deriving DecidableEq

def reachabilityGramianEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reachabilityGramianEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reachabilityGramianEncodeBHist h

def reachabilityGramianDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reachabilityGramianDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reachabilityGramianDecodeBHist tail)

private theorem ReachabilityGramianUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist, reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def reachabilityGramianFields : ReachabilityGramianUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReachabilityGramianUp.mk transition control horizon gramian transport route provenance cert
      endpoint =>
      [transition, control, horizon, gramian, transport, route, provenance, cert, endpoint]

def reachabilityGramianToEventFlow : ReachabilityGramianUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (reachabilityGramianFields x).map reachabilityGramianEncodeBHist

private def reachabilityGramianEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => reachabilityGramianEventAt index rest

def reachabilityGramianFromEventFlow (ef : EventFlow) : Option ReachabilityGramianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ReachabilityGramianUp.mk
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 0 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 1 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 2 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 3 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 4 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 5 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 6 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 7 ef))
      (reachabilityGramianDecodeBHist (reachabilityGramianEventAt 8 ef)))

private theorem ReachabilityGramianUp_single_carrier_alignment_round_trip
    (x : ReachabilityGramianUp) :
    reachabilityGramianFromEventFlow (reachabilityGramianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk transition control horizon gramian transport route provenance cert endpoint =>
      change
        some
          (ReachabilityGramianUp.mk
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist transition))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist control))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist horizon))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist gramian))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist transport))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist route))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist provenance))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist cert))
            (reachabilityGramianDecodeBHist (reachabilityGramianEncodeBHist endpoint))) =
          some
            (ReachabilityGramianUp.mk transition control horizon gramian transport route
              provenance cert endpoint)
      rw [ReachabilityGramianUp_single_carrier_alignment_decode_encode transition,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode control,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode horizon,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode gramian,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode transport,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode route,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode provenance,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode cert,
        ReachabilityGramianUp_single_carrier_alignment_decode_encode endpoint]

private theorem ReachabilityGramianUp_single_carrier_alignment_toEventFlow_injective
    {x y : ReachabilityGramianUp} :
    reachabilityGramianToEventFlow x = reachabilityGramianToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reachabilityGramianFromEventFlow (reachabilityGramianToEventFlow x) =
        reachabilityGramianFromEventFlow (reachabilityGramianToEventFlow y) :=
    congrArg reachabilityGramianFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ReachabilityGramianUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ReachabilityGramianUp_single_carrier_alignment_round_trip y)))

instance reachabilityGramianBHistCarrier : BHistCarrier ReachabilityGramianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reachabilityGramianToEventFlow
  fromEventFlow := reachabilityGramianFromEventFlow

instance reachabilityGramianChapterTasteGate : ChapterTasteGate ReachabilityGramianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reachabilityGramianFromEventFlow (reachabilityGramianToEventFlow x) = some x
    exact ReachabilityGramianUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ReachabilityGramianUp_single_carrier_alignment_toEventFlow_injective heq)

theorem ReachabilityGramianUp_single_carrier_alignment :
    Nonempty (BHistCarrier ReachabilityGramianUp) ∧
      Nonempty (ChapterTasteGate ReachabilityGramianUp) ∧
        ∃ transition control horizon gramian transport route provenance cert endpoint : BHist,
          BHistCarrier.fromEventFlow
              (BHistCarrier.toEventFlow
                (ReachabilityGramianUp.mk transition control horizon gramian transport route
                  provenance cert endpoint)) =
            some
              (ReachabilityGramianUp.mk transition control horizon gramian transport route
                provenance cert endpoint) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨reachabilityGramianBHistCarrier⟩
  constructor
  · exact ⟨reachabilityGramianChapterTasteGate⟩
  · exact
      ⟨BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, by
          change
            reachabilityGramianFromEventFlow
                (reachabilityGramianToEventFlow
                  (ReachabilityGramianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
              some
                (ReachabilityGramianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
          exact
            ReachabilityGramianUp_single_carrier_alignment_round_trip
              (ReachabilityGramianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)⟩

def ReachabilityGramianBHistCarrier [AskSetup] [PackageSetup]
    (transition control horizon gramian transport route provenance cert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory transition ∧ UnaryHistory control ∧ UnaryHistory horizon ∧
    UnaryHistory gramian ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
        Cont transport route endpoint ∧ PkgSig bundle endpoint pkg

theorem ReachabilityGramianBHistCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {transition control horizon gramian transport route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReachabilityGramianBHistCarrier transition control horizon gramian transport route provenance
        cert endpoint bundle pkg ->
      UnaryHistory transition /\ UnaryHistory control /\ UnaryHistory horizon /\
        UnaryHistory gramian /\ UnaryHistory transport /\ UnaryHistory route /\
          UnaryHistory provenance /\ UnaryHistory cert /\ UnaryHistory endpoint /\
            Cont transport route endpoint /\ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    provenanceUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩ := carrier
  exact ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    provenanceUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩

theorem ReachabilityGramianBHistCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {transition control horizon gramian transport route provenance cert endpoint exportedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReachabilityGramianBHistCarrier transition control horizon gramian transport route provenance
        cert endpoint bundle pkg ->
      Cont endpoint route exportedRead ->
        PkgSig bundle exportedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row transition ∨ hsame row control ∨ hsame row horizon ∨
                  hsame row gramian ∨ hsame row endpoint ∨ hsame row exportedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont transport route endpoint ∧
                  Cont endpoint route exportedRead ∧ PkgSig bundle exportedRead pkg)
              hsame ∧
            UnaryHistory exportedRead ∧ Cont transport route endpoint ∧
              Cont endpoint route exportedRead ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle exportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier endpointExport exportedPackage
  obtain ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    _provenanceUnary, _certUnary, endpointUnary, endpointRoute, endpointPackage⟩ := carrier
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed endpointUnary routeUnary endpointExport
  have exportedSource :
      hsame exportedRead exportedRead ∧ UnaryHistory exportedRead :=
    ⟨hsame_refl exportedRead, exportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row transition ∨ hsame row control ∨ hsame row horizon ∨
              hsame row gramian ∨ hsame row endpoint ∨ hsame row exportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport route endpoint ∧
              Cont endpoint route exportedRead ∧ PkgSig bundle exportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportedRead exportedSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, endpointExport, exportedPackage⟩
  }
  exact
    ⟨cert, exportedUnary, endpointRoute, endpointExport, endpointPackage, exportedPackage⟩

theorem ReachabilityGramianBHistCarrier_controllability_handoff [AskSetup] [PackageSetup]
    {transition control horizon gramian transport route provenance cert endpoint
      reachabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReachabilityGramianBHistCarrier transition control horizon gramian transport route provenance
        cert endpoint bundle pkg ->
      Cont transition control reachabilityRead ->
        PkgSig bundle reachabilityRead pkg ->
          UnaryHistory transition ∧ UnaryHistory control ∧ UnaryHistory horizon ∧
            UnaryHistory gramian ∧ UnaryHistory reachabilityRead ∧
              Cont transition control reachabilityRead ∧ Cont transport route endpoint ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle reachabilityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier reachabilityRoute reachabilityPackage
  obtain
    ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _certUnary, _endpointUnary, endpointRoute,
      endpointPackage⟩ := carrier
  have reachabilityUnary : UnaryHistory reachabilityRead :=
    unary_cont_closed transitionUnary controlUnary reachabilityRoute
  exact
    ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, reachabilityUnary,
      reachabilityRoute, endpointRoute, endpointPackage, reachabilityPackage⟩

end BEDC.Derived.ReachabilityGramianUp
