import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealWindowBudgetUp

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

inductive RealWindowBudgetUp : Type where
  | mk :
      (request windows dyadic handoff realSeal selector disclosure transport route provenance
        nameRow : BHist) →
      RealWindowBudgetUp
  deriving DecidableEq

def realWindowBudgetEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realWindowBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realWindowBudgetEncodeBHist h

def realWindowBudgetDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realWindowBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realWindowBudgetDecodeBHist tail)

private theorem realWindowBudget_decode_encode_bhist :
    ∀ h : BHist, realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist h) = h := by
  intro hist
  induction hist with
  | Empty =>
      rfl
  | e0 hist ih =>
      exact congrArg BHist.e0 ih
  | e1 hist ih =>
      exact congrArg BHist.e1 ih

private theorem realWindowBudget_mk_congr
    {request request' windows windows' dyadic dyadic' handoff handoff' realSeal realSeal'
      selector selector' disclosure disclosure' transport transport' route route'
      provenance provenance' nameRow nameRow' : BHist}
    (hrequest : request' = request)
    (hwindows : windows' = windows)
    (hdyadic : dyadic' = dyadic)
    (hhandoff : handoff' = handoff)
    (hrealSeal : realSeal' = realSeal)
    (hselector : selector' = selector)
    (hdisclosure : disclosure' = disclosure)
    (htransport : transport' = transport)
    (hroute : route' = route)
    (hprovenance : provenance' = provenance)
    (hnameRow : nameRow' = nameRow) :
    RealWindowBudgetUp.mk request' windows' dyadic' handoff' realSeal' selector'
        disclosure' transport' route' provenance' nameRow' =
      RealWindowBudgetUp.mk request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow := by
  cases hrequest
  cases hwindows
  cases hdyadic
  cases hhandoff
  cases hrealSeal
  cases hselector
  cases hdisclosure
  cases htransport
  cases hroute
  cases hprovenance
  cases hnameRow
  rfl

def realWindowBudgetToEventFlow : RealWindowBudgetUp → EventFlow
  | RealWindowBudgetUp.mk request windows dyadic handoff realSeal selector disclosure
      transport route provenance nameRow =>
      [realWindowBudgetEncodeBHist request,
        realWindowBudgetEncodeBHist windows,
        realWindowBudgetEncodeBHist dyadic,
        realWindowBudgetEncodeBHist handoff,
        realWindowBudgetEncodeBHist realSeal,
        realWindowBudgetEncodeBHist selector,
        realWindowBudgetEncodeBHist disclosure,
        realWindowBudgetEncodeBHist transport,
        realWindowBudgetEncodeBHist route,
        realWindowBudgetEncodeBHist provenance,
        realWindowBudgetEncodeBHist nameRow]

def realWindowBudgetFromEventFlow : EventFlow → Option RealWindowBudgetUp
  | request :: windows :: dyadic :: handoff :: realSeal :: selector :: disclosure ::
      transport :: route :: provenance :: nameRow :: [] =>
      some
        (RealWindowBudgetUp.mk
          (realWindowBudgetDecodeBHist request)
          (realWindowBudgetDecodeBHist windows)
          (realWindowBudgetDecodeBHist dyadic)
          (realWindowBudgetDecodeBHist handoff)
          (realWindowBudgetDecodeBHist realSeal)
          (realWindowBudgetDecodeBHist selector)
          (realWindowBudgetDecodeBHist disclosure)
          (realWindowBudgetDecodeBHist transport)
          (realWindowBudgetDecodeBHist route)
          (realWindowBudgetDecodeBHist provenance)
          (realWindowBudgetDecodeBHist nameRow))
  | _ => none

private theorem realWindowBudget_round_trip :
    ∀ x : RealWindowBudgetUp,
      realWindowBudgetFromEventFlow (realWindowBudgetToEventFlow x) = some x := by
  intro x
  cases x with
  | mk request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow =>
      change
        some
          (RealWindowBudgetUp.mk
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist request))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist windows))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist dyadic))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist handoff))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist realSeal))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist selector))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist disclosure))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist transport))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist route))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist provenance))
            (realWindowBudgetDecodeBHist (realWindowBudgetEncodeBHist nameRow))) =
          some
            (RealWindowBudgetUp.mk request windows dyadic handoff realSeal selector
              disclosure transport route provenance nameRow)
      exact
        congrArg some
          (realWindowBudget_mk_congr
            (realWindowBudget_decode_encode_bhist request)
            (realWindowBudget_decode_encode_bhist windows)
            (realWindowBudget_decode_encode_bhist dyadic)
            (realWindowBudget_decode_encode_bhist handoff)
            (realWindowBudget_decode_encode_bhist realSeal)
            (realWindowBudget_decode_encode_bhist selector)
            (realWindowBudget_decode_encode_bhist disclosure)
            (realWindowBudget_decode_encode_bhist transport)
            (realWindowBudget_decode_encode_bhist route)
            (realWindowBudget_decode_encode_bhist provenance)
            (realWindowBudget_decode_encode_bhist nameRow))

private theorem realWindowBudgetToEventFlow_injective {x y : RealWindowBudgetUp} :
    realWindowBudgetToEventFlow x = realWindowBudgetToEventFlow y → x = y := by
  intro heq
  have hread :
      realWindowBudgetFromEventFlow (realWindowBudgetToEventFlow x) =
        realWindowBudgetFromEventFlow (realWindowBudgetToEventFlow y) :=
    congrArg realWindowBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realWindowBudget_round_trip x).symm
      (Eq.trans hread (realWindowBudget_round_trip y)))

instance realWindowBudgetBHistCarrier : BHistCarrier RealWindowBudgetUp where
  toEventFlow := realWindowBudgetToEventFlow
  fromEventFlow := realWindowBudgetFromEventFlow

instance realWindowBudgetChapterTasteGate : ChapterTasteGate RealWindowBudgetUp where
  round_trip := realWindowBudget_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (realWindowBudgetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealWindowBudgetUp :=
  inferInstance

structure RealWindowBudgetCarrier [AskSetup] [PackageSetup]
    (request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop where
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  request_unary : UnaryHistory request
  windows_unary : UnaryHistory windows
  dyadic_unary : UnaryHistory dyadic
  handoff_unary : UnaryHistory handoff
  realSeal_unary : UnaryHistory realSeal
  selector_unary : UnaryHistory selector
  disclosure_unary : UnaryHistory disclosure
  transport_unary : UnaryHistory transport
  route_unary : UnaryHistory route
  provenance_unary : UnaryHistory provenance
  nameRow_unary : UnaryHistory nameRow
  request_windows_dyadic : Cont request windows dyadic
  dyadic_handoff_realSeal : Cont dyadic handoff realSeal
  selector_disclosure_transport : Cont selector disclosure transport
  transport_route_nameRow : Cont transport route nameRow
  provenance_pkg : PkgSig bundle provenance pkg
  nameRow_pkg : PkgSig bundle nameRow pkg

theorem RealWindowBudgetCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont handoff realSeal endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
              Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
                Cont handoff realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier handoff_realSeal_endpoint endpoint_pkg
  constructor
  · exact carrier.request_unary
  · constructor
    · exact carrier.windows_unary
    · constructor
      · exact carrier.dyadic_unary
      · constructor
        · exact carrier.handoff_unary
        · constructor
          · exact carrier.realSeal_unary
          · constructor
            · exact unary_cont_closed carrier.handoff_unary carrier.realSeal_unary
                handoff_realSeal_endpoint
            · constructor
              · exact carrier.request_windows_dyadic
              · constructor
                · exact carrier.dyadic_handoff_realSeal
                · constructor
                  · exact handoff_realSeal_endpoint
                  · constructor
                    · exact carrier.provenance_pkg
                    · exact endpoint_pkg

theorem RealWindowBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
              disclosure transport route provenance nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧ hsame row nameRow)
          hsame ∧
        UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
          UnaryHistory handoff ∧ UnaryHistory realSeal ∧ Cont request windows dyadic ∧
            Cont dyadic handoff realSeal ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierPacket :
      RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg :=
    carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
              disclosure transport route provenance nameRow bundle pkg ∧ hsame row nameRow)
          (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧ hsame row nameRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameRow ⟨carrierPacket, hsame_refl nameRow⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, unary_transport carrier.nameRow_unary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨carrier.provenance_pkg, carrier.nameRow_pkg, source.right⟩
    }
  exact
    ⟨cert, carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.realSeal_unary, carrier.request_windows_dyadic,
      carrier.dyadic_handoff_realSeal, carrier.provenance_pkg, carrier.nameRow_pkg⟩

end BEDC.Derived.RealWindowBudgetUp
