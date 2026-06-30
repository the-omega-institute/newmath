import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.DyadicIntervalCoverUp.StandardBridgePremise
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalCoverUp

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

inductive DyadicIntervalCoverUp : Type where
  | mk (L U M R V W Q A H C P N : BHist) : DyadicIntervalCoverUp
  deriving DecidableEq

def dyadicIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalCoverEncodeBHist h

def dyadicIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalCoverDecodeBHist tail)

private theorem DyadicIntervalCoverRealWindowHandoffObligation_decode :
    ∀ h : BHist, dyadicIntervalCoverDecodeBHist
      (dyadicIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalCoverFields : DyadicIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalCoverUp.mk L U M R V W Q A H C P N => [L, U, M, R, V, W, Q, A, H, C, P, N]

def dyadicIntervalCoverToEventFlow : DyadicIntervalCoverUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicIntervalCoverFields x).map dyadicIntervalCoverEncodeBHist

private def dyadicIntervalCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalCoverEventAtDefault index rest

def dyadicIntervalCoverFromEventFlow
    (ef : EventFlow) : Option DyadicIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalCoverUp.mk
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 0 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 1 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 2 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 3 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 4 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 5 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 6 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 7 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 8 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 9 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 10 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 11 ef)))

private theorem DyadicIntervalCoverRealWindowHandoffObligation_round_trip :
    ∀ x : DyadicIntervalCoverUp,
      dyadicIntervalCoverFromEventFlow
        (dyadicIntervalCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk L U M R V W Q A H C P N =>
      change
        some
          (DyadicIntervalCoverUp.mk
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist L))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist U))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist M))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist R))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist V))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist W))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist Q))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist A))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist H))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist C))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist P))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist N))) =
          some (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N)
      rw [DyadicIntervalCoverRealWindowHandoffObligation_decode L,
        DyadicIntervalCoverRealWindowHandoffObligation_decode U,
        DyadicIntervalCoverRealWindowHandoffObligation_decode M,
        DyadicIntervalCoverRealWindowHandoffObligation_decode R,
        DyadicIntervalCoverRealWindowHandoffObligation_decode V,
        DyadicIntervalCoverRealWindowHandoffObligation_decode W,
        DyadicIntervalCoverRealWindowHandoffObligation_decode Q,
        DyadicIntervalCoverRealWindowHandoffObligation_decode A,
        DyadicIntervalCoverRealWindowHandoffObligation_decode H,
        DyadicIntervalCoverRealWindowHandoffObligation_decode C,
        DyadicIntervalCoverRealWindowHandoffObligation_decode P,
        DyadicIntervalCoverRealWindowHandoffObligation_decode N]

private theorem DyadicIntervalCoverRealWindowHandoffObligation_toEventFlow_injective
    {x y : DyadicIntervalCoverUp} :
    dyadicIntervalCoverToEventFlow x = dyadicIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) =
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow y) :=
    congrArg dyadicIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicIntervalCoverRealWindowHandoffObligation_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalCoverRealWindowHandoffObligation_round_trip y)))

private theorem DyadicIntervalCoverRealWindowHandoffObligation_fields :
    ∀ x y : DyadicIntervalCoverUp,
      dyadicIntervalCoverFields x = dyadicIntervalCoverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 M1 R1 V1 W1 Q1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 M2 R2 V2 W2 Q2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicIntervalCoverBHistCarrier : BHistCarrier DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalCoverToEventFlow
  fromEventFlow := dyadicIntervalCoverFromEventFlow

instance dyadicIntervalCoverChapterTasteGate :
    ChapterTasteGate DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x
    exact DyadicIntervalCoverRealWindowHandoffObligation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalCoverRealWindowHandoffObligation_toEventFlow_injective heq)

instance dyadicIntervalCoverFieldFaithful :
    FieldFaithful DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalCoverFields
  field_faithful := DyadicIntervalCoverRealWindowHandoffObligation_fields

instance dyadicIntervalCoverNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicIntervalCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicIntervalCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalCoverChapterTasteGate

theorem DyadicIntervalCoverRealWindowHandoffObligation (x : DyadicIntervalCoverUp) :
    ∃ L U M R V W Q A H C P N : BHist,
      x = DyadicIntervalCoverUp.mk L U M R V W Q A H C P N ∧
        dyadicIntervalCoverFields x = [L, U, M, R, V, W, Q, A, H, C, P, N] ∧
          dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x ∧
            dyadicIntervalCoverEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              dyadicIntervalCoverEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      exact
        ⟨L, U, M, R, V, W, Q, A, H, C, P, N, rfl, rfl,
          DyadicIntervalCoverRealWindowHandoffObligation_round_trip
            (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N),
          rfl, rfl⟩

theorem DyadicIntervalCoverWindowMembershipTransport (x : DyadicIntervalCoverUp) :
    ∃ L U M R V W Q A H C P N : BHist,
      x = DyadicIntervalCoverUp.mk L U M R V W Q A H C P N ∧
        dyadicIntervalCoverFields x = [L, U, M, R, V, W, Q, A, H, C, P, N] ∧
          dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x ∧
            dyadicIntervalCoverEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      exact
        ⟨L, U, M, R, V, W, Q, A, H, C, P, N, rfl, rfl,
          DyadicIntervalCoverRealWindowHandoffObligation_round_trip
            (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N),
          rfl⟩

theorem DyadicIntervalCoverRealSealBoundary [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) ->
      Cont Q A sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory Q ∧ UnaryHistory A ∧ UnaryHistory sealRead ∧
            Cont Q A sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrierRows sealRoute sealPkg
  obtain ⟨_unaryL, _unaryU, _unaryM, _unaryR, _unaryV, _unaryW, unaryQ, unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, provenancePkg⟩ := carrierRows
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryA sealRoute
  exact ⟨unaryQ, unaryA, sealUnary, sealRoute, provenancePkg, sealPkg⟩

theorem DyadicIntervalCoverRootUnblockPackage [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead coverRead sealRead compactRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont M R coverRead →
            Cont coverRead A sealRead →
              Cont endpointRead sealRead compactRead →
                Cont compactRead N namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                            hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row endpointRead ∨ hsame row windowRead ∨
                                  hsame row coverRead ∨ hsame row sealRead ∨
                                    hsame row compactRead ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont L U endpointRead ∧
                            Cont W Q windowRead ∧ Cont M R coverRead ∧
                              Cont coverRead A sealRead ∧
                                Cont endpointRead sealRead compactRead ∧
                                  Cont compactRead N namedRead ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle namedRead pkg)
                        hsame ∧ UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory compactRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute windowRoute coverRoute sealRoute compactRoute namedRoute
    namedPkg
  obtain ⟨unaryL, unaryU, unaryM, unaryR, _unaryV, unaryW, unaryQ, unaryA, _unaryH,
    _unaryC, _unaryP, unaryN, provenancePkg, _localNamePkg⟩ := surface
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed unaryM unaryR coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed endpointUnary sealUnary compactRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed compactUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row endpointRead ∨
                  hsame row windowRead ∨ hsame row coverRead ∨ hsame row sealRead ∨
                    hsame row compactRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont M R coverRead ∧ Cont coverRead A sealRead ∧
                Cont endpointRead sealRead compactRead ∧ Cont compactRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr source.left))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, windowRoute, coverRoute, sealRoute, compactRoute,
          namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, endpointUnary, windowUnary, coverUnary, sealUnary, compactUnary, namedUnary⟩

theorem DyadicIntervalCoverFiniteWindowCarrier [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead coverRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont M R coverRead →
            Cont coverRead A sealRead →
              Cont sealRead N namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                          hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                            hsame row endpointRead ∨ hsame row windowRead ∨
                              hsame row coverRead ∨ hsame row sealRead ∨
                                hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L U endpointRead ∧
                          Cont W Q windowRead ∧ Cont M R coverRead ∧
                            Cont coverRead A sealRead ∧ Cont sealRead N namedRead ∧
                              PkgSig bundle namedRead pkg)
                      hsame ∧ UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute windowRoute coverRoute sealRoute namedRoute namedPkg
  obtain ⟨unaryL, unaryU, unaryM, unaryR, _unaryV, unaryW, unaryQ, unaryA, _unaryH,
    _unaryC, _unaryP, unaryN, _provenancePkg, _localNamePkg⟩ := surface
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed unaryM unaryR coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row endpointRead ∨
                hsame row windowRead ∨ hsame row coverRead ∨ hsame row sealRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont M R coverRead ∧ Cont coverRead A sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, windowRoute, coverRoute, sealRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, endpointUnary, windowUnary, coverUnary, sealUnary, namedUnary⟩

theorem DyadicIntervalCoverMembershipTransport [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N membershipRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) →
      Cont V H membershipRead →
        Cont membershipRead C transportedRead →
          PkgSig bundle transportedRead pkg →
            UnaryHistory V ∧ UnaryHistory H ∧ UnaryHistory C ∧
              UnaryHistory membershipRead ∧ UnaryHistory transportedRead ∧
                Cont V H membershipRead ∧ Cont membershipRead C transportedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle transportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrierRows membershipRoute transportedRoute transportedPkg
  obtain ⟨_unaryL, _unaryU, _unaryM, _unaryR, unaryV, _unaryW, _unaryQ,
    _unaryA, unaryH, unaryC, _unaryP, _unaryN, provenancePkg⟩ := carrierRows
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed unaryV unaryH membershipRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed membershipUnary unaryC transportedRoute
  exact
    ⟨unaryV, unaryH, unaryC, membershipUnary, transportedUnary, membershipRoute,
      transportedRoute, provenancePkg, transportedPkg⟩

theorem DyadicIntervalCoverRegularSequenceWindow_exhaustion [AskSetup] [PackageSetup]
    {M R Q V A windowRead readbackRead coverRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M -> UnaryHistory R -> UnaryHistory Q -> UnaryHistory V ->
      UnaryHistory A -> Cont M R windowRead -> Cont windowRead Q readbackRead ->
        Cont readbackRead V coverRead -> Cont coverRead A sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row V ∨
                  hsame row A ∨ hsame row windowRead ∨ hsame row readbackRead ∨
                    hsame row coverRead ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M R windowRead ∧
                  Cont windowRead Q readbackRead ∧ Cont readbackRead V coverRead ∧
                    Cont coverRead A sealRead ∧ PkgSig bundle sealRead pkg)
              hsame ∧ UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory coverRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro mUnary rUnary qUnary vUnary aUnary windowRoute readbackRoute coverRoute
    sealRoute sealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed mUnary rUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed readbackUnary vUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row V ∨
            hsame row A ∨ hsame row windowRead ∨ hsame row readbackRead ∨
              hsame row coverRead ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M R windowRead ∧ Cont windowRead Q readbackRead ∧
            Cont readbackRead V coverRead ∧ Cont coverRead A sealRead ∧
              PkgSig bundle sealRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, readbackRoute, coverRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, readbackUnary, coverUnary, sealUnary⟩

theorem DyadicIntervalCoverSealNonescape [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead readbackRead coverRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) ->
      Cont W Q windowRead ->
        Cont windowRead M readbackRead ->
          Cont readbackRead V coverRead ->
            Cont coverRead A sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory M ∧ UnaryHistory V ∧
                  UnaryHistory A ∧ UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                      Cont W Q windowRead ∧ Cont windowRead M readbackRead ∧
                        Cont readbackRead V coverRead ∧ Cont coverRead A sealRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrierRows windowRoute readbackRoute coverRoute sealRoute sealPkg
  obtain ⟨_unaryL, _unaryU, unaryM, _unaryR, unaryV, unaryW, unaryQ, unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, provenancePkg⟩ := carrierRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryM readbackRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed readbackUnary unaryV coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  exact
    ⟨unaryW, unaryQ, unaryM, unaryV, unaryA, windowUnary, readbackUnary, coverUnary,
      sealUnary, windowRoute, readbackRoute, coverRoute, sealRoute, provenancePkg, sealPkg⟩

theorem DyadicIntervalCoverBishopIntervalCompactHandoff [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead coverRead sealRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) -> Cont L U endpointRead -> Cont M R coverRead ->
      Cont coverRead A sealRead -> Cont endpointRead sealRead compactRead ->
        PkgSig bundle compactRead pkg -> UnaryHistory endpointRead ∧
          UnaryHistory coverRead ∧ UnaryHistory sealRead ∧ UnaryHistory compactRead ∧
            Cont L U endpointRead ∧ Cont M R coverRead ∧ Cont coverRead A sealRead ∧
              Cont endpointRead sealRead compactRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrierRows endpointRoute coverRoute sealRoute compactRoute compactPkg
  obtain ⟨unaryL, unaryU, unaryM, unaryR, _unaryV, _unaryW, _unaryQ, unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, provenancePkg⟩ := carrierRows
  let endpointUnary := unary_cont_closed unaryL unaryU endpointRoute
  let coverUnary := unary_cont_closed unaryM unaryR coverRoute
  let sealUnary := unary_cont_closed coverUnary unaryA sealRoute
  exact
    ⟨endpointUnary, coverUnary, sealUnary, unary_cont_closed endpointUnary sealUnary compactRoute,
      endpointRoute, coverRoute, sealRoute, compactRoute, provenancePkg, compactPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
