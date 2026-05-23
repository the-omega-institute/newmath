import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

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

inductive RealCauchyModulusUp : Type where
  | mk : (M S D Q E H C P N : BHist) -> RealCauchyModulusUp
  deriving DecidableEq

def realCauchyModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyModulusEncodeBHist h

def realCauchyModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyModulusDecodeBHist tail)

private theorem realCauchyModulus_decode_encode_bhist :
    forall h : BHist, realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realCauchyModulusEncodeBHist_injective {h k : BHist} :
    realCauchyModulusEncodeBHist h = realCauchyModulusEncodeBHist k -> h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist h) =
        realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist k) :=
    congrArg realCauchyModulusDecodeBHist heq
  exact
    Eq.trans (realCauchyModulus_decode_encode_bhist h).symm
      (Eq.trans hread (realCauchyModulus_decode_encode_bhist k))

private theorem realCauchyModulus_mk_congr
    {M1 M2 S1 S2 D1 D2 Q1 Q2 E1 E2 H1 H2 C1 C2 P1 P2 N1 N2 : BHist}
    (hM : M1 = M2) (hS : S1 = S2) (hD : D1 = D2) (hQ : Q1 = Q2)
    (hE : E1 = E2) (hH : H1 = H2) (hC : C1 = C2) (hP : P1 = P2)
    (hN : N1 = N2) :
    RealCauchyModulusUp.mk M1 S1 D1 Q1 E1 H1 C1 P1 N1 =
      RealCauchyModulusUp.mk M2 S2 D2 Q2 E2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realCauchyModulusFields : RealCauchyModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyModulusUp.mk M S D Q E H C P N => [M, S, D, Q, E, H, C, P, N]

def realCauchyModulusToEventFlow : RealCauchyModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realCauchyModulusEncodeBHist (realCauchyModulusFields x)

def realCauchyModulusFromEventFlow : EventFlow -> Option RealCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RealCauchyModulusUp.mk
                                              (realCauchyModulusDecodeBHist M)
                                              (realCauchyModulusDecodeBHist S)
                                              (realCauchyModulusDecodeBHist D)
                                              (realCauchyModulusDecodeBHist Q)
                                              (realCauchyModulusDecodeBHist E)
                                              (realCauchyModulusDecodeBHist H)
                                              (realCauchyModulusDecodeBHist C)
                                              (realCauchyModulusDecodeBHist P)
                                              (realCauchyModulusDecodeBHist N))
                                      | _ :: _ => none

private theorem realCauchyModulus_round_trip :
    forall x : RealCauchyModulusUp,
      realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D Q E H C P N =>
      change
        some
          (RealCauchyModulusUp.mk
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist M))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist S))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist D))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist Q))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist E))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist H))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist C))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist P))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist N))) =
          some (RealCauchyModulusUp.mk M S D Q E H C P N)
      exact
        congrArg some
          (realCauchyModulus_mk_congr
            (realCauchyModulus_decode_encode_bhist M)
            (realCauchyModulus_decode_encode_bhist S)
            (realCauchyModulus_decode_encode_bhist D)
            (realCauchyModulus_decode_encode_bhist Q)
            (realCauchyModulus_decode_encode_bhist E)
            (realCauchyModulus_decode_encode_bhist H)
            (realCauchyModulus_decode_encode_bhist C)
            (realCauchyModulus_decode_encode_bhist P)
            (realCauchyModulus_decode_encode_bhist N))

private theorem realCauchyModulusToEventFlow_injective {x y : RealCauchyModulusUp} :
    realCauchyModulusToEventFlow x = realCauchyModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) =
        realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow y) :=
    congrArg realCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyModulus_round_trip x).symm
      (Eq.trans hread (realCauchyModulus_round_trip y)))

instance realCauchyModulusBHistCarrier : BHistCarrier RealCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyModulusToEventFlow
  fromEventFlow := realCauchyModulusFromEventFlow

instance realCauchyModulusChapterTasteGate : ChapterTasteGate RealCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) = some x
    exact realCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyModulusToEventFlow_injective heq)

instance realCauchyModulusNontrivial : Nontrivial RealCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyModulusChapterTasteGate

theorem RealCauchyModulusTasteGate_single_carrier_alignment :
    (forall h : BHist, realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist h) = h) ∧
      (forall x : RealCauchyModulusUp,
        realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) = some x) ∧
        (forall x y : RealCauchyModulusUp,
          realCauchyModulusToEventFlow x = realCauchyModulusToEventFlow y -> x = y) ∧
          realCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realCauchyModulus_decode_encode_bhist
  · constructor
    · exact realCauchyModulus_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk M1 S1 D1 Q1 E1 H1 C1 P1 N1 =>
            cases y with
            | mk M2 S2 D2 Q2 E2 H2 C2 P2 N2 =>
                change
                  [realCauchyModulusEncodeBHist M1, realCauchyModulusEncodeBHist S1,
                      realCauchyModulusEncodeBHist D1, realCauchyModulusEncodeBHist Q1,
                      realCauchyModulusEncodeBHist E1, realCauchyModulusEncodeBHist H1,
                      realCauchyModulusEncodeBHist C1, realCauchyModulusEncodeBHist P1,
                      realCauchyModulusEncodeBHist N1] =
                    [realCauchyModulusEncodeBHist M2, realCauchyModulusEncodeBHist S2,
                      realCauchyModulusEncodeBHist D2, realCauchyModulusEncodeBHist Q2,
                      realCauchyModulusEncodeBHist E2, realCauchyModulusEncodeBHist H2,
                      realCauchyModulusEncodeBHist C2, realCauchyModulusEncodeBHist P2,
                      realCauchyModulusEncodeBHist N2] at heq
                injection heq with hM t1
                injection t1 with hS t2
                injection t2 with hD t3
                injection t3 with hQ t4
                injection t4 with hE t5
                injection t5 with hH t6
                injection t6 with hC t7
                injection t7 with hP t8
                injection t8 with hN _
                exact
                  realCauchyModulus_mk_congr
                    (realCauchyModulusEncodeBHist_injective hM)
                    (realCauchyModulusEncodeBHist_injective hS)
                    (realCauchyModulusEncodeBHist_injective hD)
                    (realCauchyModulusEncodeBHist_injective hQ)
                    (realCauchyModulusEncodeBHist_injective hE)
                    (realCauchyModulusEncodeBHist_injective hH)
                    (realCauchyModulusEncodeBHist_injective hC)
                    (realCauchyModulusEncodeBHist_injective hP)
                    (realCauchyModulusEncodeBHist_injective hN)
      · rfl

def RealCauchyModulusCarrier [AskSetup] [PackageSetup]
    (modulus windows dyadic readback sealRow transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
          Cont sealRow routes provenance ∧ PkgSig bundle provenance pkg ∧
            SemanticNameCert
              (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
              (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
              (fun row row' : BHist => hsame row row')

namespace TasteGate

theorem RealCauchyModulusCarrier_window_modulus_route [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      routeConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      Cont sealRow routes routeConsumer ->
        PkgSig bundle routeConsumer pkg ->
          UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory sealRow ∧ UnaryHistory routeConsumer ∧ Cont modulus windows dyadic ∧
              Cont dyadic readback sealRow ∧ Cont sealRow routes routeConsumer ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle routeConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeConsumerCont routeConsumerPkg
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, _readbackUnary, sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have routeConsumerUnary : UnaryHistory routeConsumer :=
    unary_cont_closed sealUnary routesUnary routeConsumerCont
  exact
    ⟨modulusUnary, windowsUnary, dyadicUnary, sealUnary, routeConsumerUnary,
      modulusWindowRoute, dyadicReadbackRoute, routeConsumerCont, provenancePkg,
      routeConsumerPkg⟩

end TasteGate

theorem RealCauchyModulusCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transports ∧
          UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
            Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
              Cont sealRow routes provenance ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig NameCert
  intro carrier
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    transportsUnary, routesUnary, provenanceUnary, localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, sealRoute, provenancePkg, _localSemantic⟩ := carrier
  exact
    ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary, transportsUnary,
      routesUnary, provenanceUnary, localCertUnary, modulusWindowRoute, dyadicReadbackRoute,
      sealRoute, provenancePkg⟩

theorem RealCauchyModulusCarrier_threshold_stability [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert modulus'
      windows' dyadic' readback' sealRow' transports' routes' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      hsame modulus modulus' →
        hsame windows windows' →
          hsame dyadic dyadic' →
            hsame readback readback' →
              hsame sealRow sealRow' →
                hsame transports transports' →
                  hsame routes routes' →
                    hsame provenance provenance' →
                      hsame localCert localCert' →
                        Cont modulus' windows' dyadic' →
                          Cont dyadic' readback' sealRow' →
                            Cont sealRow' routes' provenance' →
                              PkgSig bundle provenance' pkg →
                                RealCauchyModulusCarrier modulus' windows' dyadic' readback'
                                    sealRow' transports' routes' provenance' localCert' bundle
                                    pkg ∧
                                  hsame sealRow sealRow' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier sameModulus sameWindows sameDyadic sameReadback sameSeal sameTransports
  intro sameRoutes sameProvenance sameLocalCert routeMod routeRead routeSeal pkgProvenance
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    transportsUnary, routesUnary, provenanceUnary, localCertUnary, _routeMod, _routeRead,
      _routeSeal, _pkgProvenance, _localSemantic⟩ := carrier
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have localSourceWitness :
      hsame localCert' localCert' ∧ UnaryHistory localCert' :=
    ⟨hsame_refl localCert', localCertUnary'⟩
  have localSemantic' :
      SemanticNameCert
        (fun row : BHist => hsame row localCert' ∧ UnaryHistory row)
        (fun row : BHist => UnaryHistory row ∧ hsame row localCert')
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance' pkg)
        (fun row row' : BHist => hsame row row') :=
    {
      core := {
        carrier_inhabited := ⟨localCert', localSourceWitness⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨source.right, source.left⟩
      ledger_sound := by
        intro row source
        exact ⟨source.right, pkgProvenance⟩
    }
  exact
    ⟨⟨modulusUnary', windowsUnary', dyadicUnary', readbackUnary', sealUnary',
      transportsUnary', routesUnary', provenanceUnary', localCertUnary', routeMod, routeRead,
      routeSeal, pkgProvenance, localSemantic'⟩, sameSeal⟩

theorem RealCauchyModulusCarrier_precision_induction [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      precision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory precision ->
        exists refinedWindows refinedDyadic refinedSeal : BHist,
          Cont modulus precision refinedWindows ∧ Cont refinedWindows dyadic refinedDyadic ∧
            Cont refinedDyadic readback refinedSeal ∧ UnaryHistory refinedWindows ∧
              UnaryHistory refinedDyadic ∧ UnaryHistory refinedSeal ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier precisionUnary
  obtain ⟨modulusUnary, _windowsUnary, dyadicUnary, readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _modulusRoute,
      _dyadicRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  let refinedWindows : BHist := BEDC.FKernel.Cont.append modulus precision
  let refinedDyadic : BHist := BEDC.FKernel.Cont.append refinedWindows dyadic
  let refinedSeal : BHist := BEDC.FKernel.Cont.append refinedDyadic readback
  have windowsCont : Cont modulus precision refinedWindows := rfl
  have refinedWindowsUnary : UnaryHistory refinedWindows :=
    unary_cont_closed modulusUnary precisionUnary windowsCont
  have dyadicCont : Cont refinedWindows dyadic refinedDyadic := rfl
  have refinedDyadicUnary : UnaryHistory refinedDyadic :=
    unary_cont_closed refinedWindowsUnary dyadicUnary dyadicCont
  have sealCont : Cont refinedDyadic readback refinedSeal := rfl
  have refinedSealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed refinedDyadicUnary readbackUnary sealCont
  exact
    ⟨refinedWindows, refinedDyadic, refinedSeal, windowsCont, dyadicCont, sealCont,
      refinedWindowsUnary, refinedDyadicUnary, refinedSealUnary, provenancePkg⟩

theorem RealCauchyModulusCarrier_window_monotonicity [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      strongerRequest strongerWindows strongerDyadic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory strongerRequest ->
        Cont windows strongerRequest strongerWindows ->
          Cont strongerWindows dyadic strongerDyadic ->
            UnaryHistory windows ∧ UnaryHistory strongerWindows ∧ UnaryHistory dyadic ∧
              UnaryHistory strongerDyadic ∧ Cont modulus windows dyadic ∧
                Cont windows strongerRequest strongerWindows ∧
                  Cont strongerWindows dyadic strongerDyadic ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier strongerRequestUnary strongerWindowCont strongerDyadicCont
  obtain ⟨_modulusUnary, windowsUnary, dyadicUnary, _readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have strongerWindowsUnary : UnaryHistory strongerWindows :=
    unary_cont_closed windowsUnary strongerRequestUnary strongerWindowCont
  have strongerDyadicUnary : UnaryHistory strongerDyadic :=
    unary_cont_closed strongerWindowsUnary dyadicUnary strongerDyadicCont
  exact
    ⟨windowsUnary, strongerWindowsUnary, dyadicUnary, strongerDyadicUnary,
      modulusWindowRoute, strongerWindowCont, strongerDyadicCont, provenancePkg⟩

theorem RealCauchyModulusCarrier_tail_threshold_determinacy [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      strongerRequest strongerWindows strongerDyadic strongerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory strongerRequest ->
        Cont windows strongerRequest strongerWindows ->
          Cont strongerWindows dyadic strongerDyadic ->
            Cont strongerDyadic readback strongerSeal ->
              UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory strongerWindows ∧
                UnaryHistory strongerDyadic ∧ UnaryHistory strongerSeal ∧
                  Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
                    Cont windows strongerRequest strongerWindows ∧
                      Cont strongerWindows dyadic strongerDyadic ∧
                        Cont strongerDyadic readback strongerSeal ∧
                          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier strongerRequestUnary strongerWindowCont strongerDyadicCont strongerSealCont
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have strongerWindowsUnary : UnaryHistory strongerWindows :=
    unary_cont_closed windowsUnary strongerRequestUnary strongerWindowCont
  have strongerDyadicUnary : UnaryHistory strongerDyadic :=
    unary_cont_closed strongerWindowsUnary dyadicUnary strongerDyadicCont
  have strongerSealUnary : UnaryHistory strongerSeal :=
    unary_cont_closed strongerDyadicUnary readbackUnary strongerSealCont
  exact
    ⟨modulusUnary, windowsUnary, strongerWindowsUnary, strongerDyadicUnary,
      strongerSealUnary, modulusWindowRoute, dyadicReadbackRoute, strongerWindowCont,
      strongerDyadicCont, strongerSealCont, provenancePkg⟩

theorem RealCauchyModulusCarrier_seal_handoff [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      routeConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      Cont sealRow routes routeConsumer →
        PkgSig bundle routeConsumer pkg →
          UnaryHistory sealRow ∧ UnaryHistory routes ∧ UnaryHistory routeConsumer ∧
            Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
              Cont sealRow routes routeConsumer ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle routeConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier routeConsumerCont routeConsumerPkg
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, _readbackUnary, sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have routeConsumerUnary : UnaryHistory routeConsumer :=
    unary_cont_closed sealUnary routesUnary routeConsumerCont
  exact
    ⟨sealUnary, routesUnary, routeConsumerUnary, modulusWindowRoute, dyadicReadbackRoute,
      routeConsumerCont, provenancePkg, routeConsumerPkg⟩

theorem RealCauchyModulusCarrier_ledger_exhaustion [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes
        provenance localCert bundle pkg ->
      Cont sealRow routes consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
                UnaryHistory consumer ∧ Cont modulus windows dyadic ∧
                  Cont dyadic readback sealRow ∧ Cont sealRow routes consumer ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sealRouteConsumer consumerPkg
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    transportsUnary, routesUnary, provenanceUnary, localCertUnary, modulusWindowDyadic,
      dyadicReadbackSeal, _sealRouteProvenance, provenancePkg, _localSemantic⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary routesUnary sealRouteConsumer
  exact
    ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary, transportsUnary,
      routesUnary, provenanceUnary, localCertUnary, consumerUnary, modulusWindowDyadic,
      dyadicReadbackSeal, sealRouteConsumer, provenancePkg, consumerPkg⟩

theorem RealCauchyModulusCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      routeConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      Cont sealRow routes routeConsumer →
        PkgSig bundle routeConsumer pkg →
          UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory routeConsumer ∧
            Cont dyadic readback sealRow ∧ Cont sealRow routes routeConsumer ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle routeConsumer pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
                  (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                  (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert
  intro carrier routeConsumerCont routeConsumerPkg
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, _modulusRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, localSemantic⟩ := carrier
  have routeConsumerUnary : UnaryHistory routeConsumer :=
    unary_cont_closed sealUnary routesUnary routeConsumerCont
  exact
    ⟨readbackUnary, sealUnary, routeConsumerUnary, dyadicReadbackRoute, routeConsumerCont,
      provenancePkg, routeConsumerPkg, localSemantic⟩

end BEDC.Derived.RealCauchyModulusUp
