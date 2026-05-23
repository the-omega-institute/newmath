import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompilerClassifierRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompilerClassifierRouteUp : Type where
  | mk :
      (source target membership morphism nameMorphism graph extPres sigRel trace transport
        route provenance name : BHist) ->
        CompilerClassifierRouteUp
  deriving DecidableEq

private def compilerClassifierRouteEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compilerClassifierRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compilerClassifierRouteEncodeBHist h

private def compilerClassifierRouteDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compilerClassifierRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compilerClassifierRouteDecodeBHist tail)

private def compilerClassifierRouteNthRawEvent : EventFlow -> Nat -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => compilerClassifierRouteNthRawEvent tail n

private theorem compilerClassifierRoute_decode_encode_bhist :
    ∀ h : BHist,
      compilerClassifierRouteDecodeBHist (compilerClassifierRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem compilerClassifierRoute_mk_congr
    {source source' target target' membership membership' morphism morphism'
      nameMorphism nameMorphism' graph graph' extPres extPres' sigRel sigRel'
      trace trace' transport transport' route route' provenance provenance' name name' :
        BHist}
    (hsource : source' = source)
    (htarget : target' = target)
    (hmembership : membership' = membership)
    (hmorphism : morphism' = morphism)
    (hnameMorphism : nameMorphism' = nameMorphism)
    (hgraph : graph' = graph)
    (hextPres : extPres' = extPres)
    (hsigRel : sigRel' = sigRel)
    (htrace : trace' = trace)
    (htransport : transport' = transport)
    (hroute : route' = route)
    (hprovenance : provenance' = provenance)
    (hname : name' = name) :
    CompilerClassifierRouteUp.mk source' target' membership' morphism' nameMorphism'
        graph' extPres' sigRel' trace' transport' route' provenance' name' =
      CompilerClassifierRouteUp.mk source target membership morphism nameMorphism graph
        extPres sigRel trace transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hsource
  cases htarget
  cases hmembership
  cases hmorphism
  cases hnameMorphism
  cases hgraph
  cases hextPres
  cases hsigRel
  cases htrace
  cases htransport
  cases hroute
  cases hprovenance
  cases hname
  rfl

private def compilerClassifierRouteFields : CompilerClassifierRouteUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompilerClassifierRouteUp.mk source target membership morphism nameMorphism graph extPres
      sigRel trace transport route provenance name =>
      [source, target, membership, morphism, nameMorphism, graph, extPres, sigRel, trace,
        transport, route, provenance, name]

private def compilerClassifierRouteToEventFlow : CompilerClassifierRouteUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompilerClassifierRouteUp.mk source target membership morphism nameMorphism graph extPres
      sigRel trace transport route provenance name =>
      [compilerClassifierRouteEncodeBHist source,
        compilerClassifierRouteEncodeBHist target,
        compilerClassifierRouteEncodeBHist membership,
        compilerClassifierRouteEncodeBHist morphism,
        compilerClassifierRouteEncodeBHist nameMorphism,
        compilerClassifierRouteEncodeBHist graph,
        compilerClassifierRouteEncodeBHist extPres,
        compilerClassifierRouteEncodeBHist sigRel,
        compilerClassifierRouteEncodeBHist trace,
        compilerClassifierRouteEncodeBHist transport,
        compilerClassifierRouteEncodeBHist route,
        compilerClassifierRouteEncodeBHist provenance,
        compilerClassifierRouteEncodeBHist name]

private def compilerClassifierRouteFromEventFlow (ef : EventFlow) :
    Option CompilerClassifierRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompilerClassifierRouteUp.mk
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 0))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 1))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 2))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 3))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 4))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 5))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 6))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 7))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 8))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 9))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 10))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 11))
      (compilerClassifierRouteDecodeBHist (compilerClassifierRouteNthRawEvent ef 12)))

private theorem compilerClassifierRoute_round_trip :
    ∀ x : CompilerClassifierRouteUp,
      compilerClassifierRouteFromEventFlow (compilerClassifierRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target membership morphism nameMorphism graph extPres sigRel trace transport
      route provenance name =>
      exact
        congrArg some
          (compilerClassifierRoute_mk_congr
            (compilerClassifierRoute_decode_encode_bhist source)
            (compilerClassifierRoute_decode_encode_bhist target)
            (compilerClassifierRoute_decode_encode_bhist membership)
            (compilerClassifierRoute_decode_encode_bhist morphism)
            (compilerClassifierRoute_decode_encode_bhist nameMorphism)
            (compilerClassifierRoute_decode_encode_bhist graph)
            (compilerClassifierRoute_decode_encode_bhist extPres)
            (compilerClassifierRoute_decode_encode_bhist sigRel)
            (compilerClassifierRoute_decode_encode_bhist trace)
            (compilerClassifierRoute_decode_encode_bhist transport)
            (compilerClassifierRoute_decode_encode_bhist route)
            (compilerClassifierRoute_decode_encode_bhist provenance)
            (compilerClassifierRoute_decode_encode_bhist name))

private theorem compilerClassifierRouteToEventFlow_injective
    {x y : CompilerClassifierRouteUp} :
    compilerClassifierRouteToEventFlow x = compilerClassifierRouteToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compilerClassifierRouteFromEventFlow (compilerClassifierRouteToEventFlow x) =
        compilerClassifierRouteFromEventFlow (compilerClassifierRouteToEventFlow y) :=
    congrArg compilerClassifierRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compilerClassifierRoute_round_trip x).symm
      (Eq.trans hread (compilerClassifierRoute_round_trip y)))

private theorem compilerClassifierRoute_field_faithful :
    ∀ x y : CompilerClassifierRouteUp,
      compilerClassifierRouteFields x = compilerClassifierRouteFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source target membership morphism nameMorphism graph extPres sigRel trace transport
      route provenance name =>
      cases y with
      | mk source' target' membership' morphism' nameMorphism' graph' extPres' sigRel'
          trace' transport' route' provenance' name' =>
          cases hfields
          rfl

instance compilerClassifierRouteBHistCarrier : BHistCarrier CompilerClassifierRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compilerClassifierRouteToEventFlow
  fromEventFlow := compilerClassifierRouteFromEventFlow

instance compilerClassifierRouteChapterTasteGateInst : ChapterTasteGate CompilerClassifierRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compilerClassifierRouteFromEventFlow (compilerClassifierRouteToEventFlow x) = some x
    exact compilerClassifierRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compilerClassifierRouteToEventFlow_injective heq)

instance compilerClassifierRouteFieldFaithful : FieldFaithful CompilerClassifierRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compilerClassifierRouteFields
  field_faithful := compilerClassifierRoute_field_faithful

instance compilerClassifierRouteNontrivial : Nontrivial CompilerClassifierRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompilerClassifierRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CompilerClassifierRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem compilerClassifierRouteChapterTasteGate :
    Nonempty (ChapterTasteGate CompilerClassifierRouteUp) ∧
      Nonempty (FieldFaithful CompilerClassifierRouteUp) ∧
        Nonempty (Nontrivial CompilerClassifierRouteUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨compilerClassifierRouteChapterTasteGateInst⟩,
      ⟨compilerClassifierRouteFieldFaithful⟩,
      ⟨compilerClassifierRouteNontrivial⟩⟩

theorem CompilerClassifierRouteNameCertObligations [AskSetup] [PackageSetup]
    {S T A M K G E Q L H C P N graphRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle P pkg ->
      Cont G E graphRead ->
        Cont graphRead Q routeRead ->
          hsame routeRead C ->
            compilerClassifierRouteFields
                (CompilerClassifierRouteUp.mk S T A M K G E Q L H C P N) =
              [S, T, A, M, K, G, E, Q, L, H, C, P, N] ∧
              SemanticNameCert
                (fun row : BHist => hsame row routeRead)
                (fun row : BHist =>
                  hsame row routeRead ∧ Cont G E graphRead ∧ Cont graphRead Q routeRead)
                (fun row : BHist =>
                  hsame row routeRead ∧ PkgSig bundle P pkg ∧ hsame routeRead C)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg SemanticNameCert ProbeBundle SigRel
  intro pkgSig graphRoute routeRoute sameRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead)
        (fun row : BHist =>
          hsame row routeRead ∧ Cont G E graphRead ∧ Cont graphRead Q routeRead)
        (fun row : BHist =>
          hsame row routeRead ∧ PkgSig bundle P pkg ∧ hsame routeRead C)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead (hsame_refl routeRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact ⟨source, graphRoute, routeRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source, pkgSig, sameRoute⟩
  }
  exact ⟨rfl, cert⟩

theorem CompilerClassifierRouteSharedRowRejection
    {S T A M K G E Q L H C P N graphRead routeRead strayGraph : BHist} :
    compilerClassifierRouteFields
        (CompilerClassifierRouteUp.mk S T A M K G E Q L H C P N) =
      [S, T, A, M, K, G, E, Q, L, H, C, P, N] ->
      Cont G E graphRead ->
        Cont graphRead Q routeRead ->
          hsame strayGraph G ->
            hsame routeRead C ->
              hsame strayGraph G ∧ Cont G E graphRead ∧ Cont graphRead Q routeRead ∧
                hsame routeRead C := by
  -- BEDC touchpoint anchor: BHist Cont hsame Ext SigRel
  intro _fields graphRoute routeRoute sameStray sameRoute
  exact ⟨sameStray, graphRoute, routeRoute, sameRoute⟩

end BEDC.Derived.CompilerClassifierRouteUp
