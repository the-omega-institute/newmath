import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalModulusNormalizationSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalModulusNormalizationSealUp : Type where
  | mk :
      (leftSchedule rightSchedule modulusSeal sharedWindow dyadicLedger regseqReadback realSeal
        transport routes provenance handoffLedger nameCert : BHist) →
      CofinalModulusNormalizationSealUp
  deriving DecidableEq

def cofinalModulusNormalizationSealFields :
    CofinalModulusNormalizationSealUp → List BHist
  | CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal sharedWindow
      dyadicLedger regseqReadback realSeal transport routes provenance handoffLedger nameCert =>
      [leftSchedule, rightSchedule, modulusSeal, sharedWindow, dyadicLedger, regseqReadback,
        realSeal, transport, routes, provenance, handoffLedger, nameCert]

def cofinalModulusNormalizationSealEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalModulusNormalizationSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalModulusNormalizationSealEncodeBHist h

def cofinalModulusNormalizationSealDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalModulusNormalizationSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalModulusNormalizationSealDecodeBHist tail)

private theorem cofinalModulusNormalizationSeal_decode_encode_bhist :
    ∀ h : BHist,
      cofinalModulusNormalizationSealDecodeBHist
          (cofinalModulusNormalizationSealEncodeBHist h) =
        h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cofinalModulusNormalizationSeal_mk_congr
    {leftSchedule leftSchedule' rightSchedule rightSchedule' modulusSeal modulusSeal'
      sharedWindow sharedWindow' dyadicLedger dyadicLedger' regseqReadback regseqReadback'
      realSeal realSeal' transport transport' routes routes' provenance provenance'
      handoffLedger handoffLedger' nameCert nameCert' : BHist}
    (hLeftSchedule : leftSchedule' = leftSchedule)
    (hRightSchedule : rightSchedule' = rightSchedule)
    (hModulusSeal : modulusSeal' = modulusSeal)
    (hSharedWindow : sharedWindow' = sharedWindow)
    (hDyadicLedger : dyadicLedger' = dyadicLedger)
    (hRegseqReadback : regseqReadback' = regseqReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hHandoffLedger : handoffLedger' = handoffLedger)
    (hNameCert : nameCert' = nameCert) :
    CofinalModulusNormalizationSealUp.mk leftSchedule' rightSchedule' modulusSeal'
        sharedWindow' dyadicLedger' regseqReadback' realSeal' transport' routes'
        provenance' handoffLedger' nameCert' =
      CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal
        sharedWindow dyadicLedger regseqReadback realSeal transport routes provenance
        handoffLedger nameCert := by
  cases hLeftSchedule
  cases hRightSchedule
  cases hModulusSeal
  cases hSharedWindow
  cases hDyadicLedger
  cases hRegseqReadback
  cases hRealSeal
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hHandoffLedger
  cases hNameCert
  rfl

def cofinalModulusNormalizationSealToEventFlow :
    CofinalModulusNormalizationSealUp → EventFlow
  | CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal sharedWindow
      dyadicLedger regseqReadback realSeal transport routes provenance handoffLedger nameCert =>
      [[BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist leftSchedule,
        [BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist rightSchedule,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist modulusSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist sharedWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist regseqReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist handoffLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist nameCert]

private def cofinalModulusNormalizationSealEventAtDefault :
    Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cofinalModulusNormalizationSealEventAtDefault index rest

def cofinalModulusNormalizationSealFromEventFlow
    (ef : EventFlow) : Option CofinalModulusNormalizationSealUp :=
  some
    (CofinalModulusNormalizationSealUp.mk
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 1 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 3 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 5 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 7 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 9 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 11 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 13 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 15 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 17 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 19 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 21 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 23 ef)))

private theorem cofinalModulusNormalizationSeal_round_trip :
    ∀ x : CofinalModulusNormalizationSealUp,
      cofinalModulusNormalizationSealFromEventFlow
          (cofinalModulusNormalizationSealToEventFlow x) =
        some x := by
  intro x
  cases x with
  | mk leftSchedule rightSchedule modulusSeal sharedWindow dyadicLedger regseqReadback
      realSeal transport routes provenance handoffLedger nameCert =>
      change
        some
            (CofinalModulusNormalizationSealUp.mk
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist leftSchedule))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist rightSchedule))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist modulusSeal))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist sharedWindow))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist dyadicLedger))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist regseqReadback))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist realSeal))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist transport))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist routes))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist provenance))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist handoffLedger))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist nameCert))) =
          some
            (CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal
              sharedWindow dyadicLedger regseqReadback realSeal transport routes provenance
              handoffLedger nameCert)
      exact
        congrArg some
          (cofinalModulusNormalizationSeal_mk_congr
            (cofinalModulusNormalizationSeal_decode_encode_bhist leftSchedule)
            (cofinalModulusNormalizationSeal_decode_encode_bhist rightSchedule)
            (cofinalModulusNormalizationSeal_decode_encode_bhist modulusSeal)
            (cofinalModulusNormalizationSeal_decode_encode_bhist sharedWindow)
            (cofinalModulusNormalizationSeal_decode_encode_bhist dyadicLedger)
            (cofinalModulusNormalizationSeal_decode_encode_bhist regseqReadback)
            (cofinalModulusNormalizationSeal_decode_encode_bhist realSeal)
            (cofinalModulusNormalizationSeal_decode_encode_bhist transport)
            (cofinalModulusNormalizationSeal_decode_encode_bhist routes)
            (cofinalModulusNormalizationSeal_decode_encode_bhist provenance)
            (cofinalModulusNormalizationSeal_decode_encode_bhist handoffLedger)
            (cofinalModulusNormalizationSeal_decode_encode_bhist nameCert))

private theorem cofinalModulusNormalizationSealToEventFlow_injective
    {x y : CofinalModulusNormalizationSealUp} :
    cofinalModulusNormalizationSealToEventFlow x =
      cofinalModulusNormalizationSealToEventFlow y →
        x = y := by
  intro heq
  have hread :
      cofinalModulusNormalizationSealFromEventFlow
          (cofinalModulusNormalizationSealToEventFlow x) =
        cofinalModulusNormalizationSealFromEventFlow
          (cofinalModulusNormalizationSealToEventFlow y) :=
    congrArg cofinalModulusNormalizationSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalModulusNormalizationSeal_round_trip x).symm
      (Eq.trans hread (cofinalModulusNormalizationSeal_round_trip y)))

instance cofinalModulusNormalizationSealBHistCarrier :
    BHistCarrier CofinalModulusNormalizationSealUp where
  toEventFlow := cofinalModulusNormalizationSealToEventFlow
  fromEventFlow := cofinalModulusNormalizationSealFromEventFlow

instance cofinalModulusNormalizationSealChapterTasteGate :
    ChapterTasteGate CofinalModulusNormalizationSealUp where
  round_trip := by
    intro x
    exact cofinalModulusNormalizationSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalModulusNormalizationSealToEventFlow_injective heq)

instance cofinalModulusNormalizationSealFieldFaithful :
    FieldFaithful CofinalModulusNormalizationSealUp where
  fields := cofinalModulusNormalizationSealFields
  field_faithful := by
    intro x y h
    cases x with
    | mk leftSchedule₁ rightSchedule₁ modulusSeal₁ sharedWindow₁ dyadicLedger₁
        regseqReadback₁ realSeal₁ transport₁ routes₁ provenance₁ handoffLedger₁ nameCert₁ =>
        cases y with
        | mk leftSchedule₂ rightSchedule₂ modulusSeal₂ sharedWindow₂ dyadicLedger₂
            regseqReadback₂ realSeal₂ transport₂ routes₂ provenance₂ handoffLedger₂ nameCert₂ =>
            injection h with hLeftSchedule hRest₁
            injection hRest₁ with hRightSchedule hRest₂
            injection hRest₂ with hModulusSeal hRest₃
            injection hRest₃ with hSharedWindow hRest₄
            injection hRest₄ with hDyadicLedger hRest₅
            injection hRest₅ with hRegseqReadback hRest₆
            injection hRest₆ with hRealSeal hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hRoutes hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hHandoffLedger hRest₁₁
            injection hRest₁₁ with hNameCert _
            cases hLeftSchedule
            cases hRightSchedule
            cases hModulusSeal
            cases hSharedWindow
            cases hDyadicLedger
            cases hRegseqReadback
            cases hRealSeal
            cases hTransport
            cases hRoutes
            cases hProvenance
            cases hHandoffLedger
            cases hNameCert
            rfl

instance cofinalModulusNormalizationSealNontrivial :
    Nontrivial CofinalModulusNormalizationSealUp where
  witness_pair := by
    refine
      ⟨CofinalModulusNormalizationSealUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty,
        CofinalModulusNormalizationSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty, ?_⟩
    intro h
    cases h

def cofinalModulusNormalizationSealClassifier
    (x y : CofinalModulusNormalizationSealUp) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  match x, y with
  | CofinalModulusNormalizationSealUp.mk A B M W D R E _H _C _P L _N,
      CofinalModulusNormalizationSealUp.mk A' B' M' W' D' R' E' _H' _C' _P' L' _N' =>
      hsame
        (append (append (append (append (append (append A B) M) W) D) R)
          (append E L))
        (append (append (append (append (append (append A' B') M') W') D') R')
          (append E' L'))

theorem cofinalModulusNormalizationSealClassifier_route
    {x y : CofinalModulusNormalizationSealUp} {support publicRead : BHist} :
    cofinalModulusNormalizationSealClassifier x y →
      match x, y with
      | CofinalModulusNormalizationSealUp.mk A B M W D R E _H _C _P L _N,
          CofinalModulusNormalizationSealUp.mk A' B' M' W' D' R' E' _H' _C' _P' L' _N' =>
          Cont
            (append (append (append (append (append (append A B) M) W) D) R)
              (append E L))
            support publicRead →
              Cont
                (append (append (append (append (append (append A' B') M') W') D') R')
                  (append E' L'))
                support publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro classifier
  cases x with
  | mk A B M W D R E H C P L N =>
      cases y with
      | mk A' B' M' W' D' R' E' H' C' P' L' N' =>
          intro route
          change publicRead =
            append
              (append (append (append (append (append (append A' B') M') W') D') R')
                (append E' L'))
              support
          exact route.trans (congrArg (fun row => append row support) classifier)

theorem CofinalModulusNormalizationSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CofinalModulusNormalizationSealUp) ∧
      Nonempty (FieldFaithful CofinalModulusNormalizationSealUp) ∧
        Nonempty (Nontrivial CofinalModulusNormalizationSealUp) := by
  constructor
  · exact ⟨cofinalModulusNormalizationSealChapterTasteGate⟩
  · constructor
    · exact ⟨cofinalModulusNormalizationSealFieldFaithful⟩
    · exact ⟨cofinalModulusNormalizationSealNontrivial⟩

theorem CofinalModulusNormalizationSeal_namecert_obligations [AskSetup] [PackageSetup]
    {A B M W D R E H C P L N sharedRead dyadicRead regularRead sealRead terminalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] →
      Cont A B M →
        Cont M W sharedRead →
          Cont sharedRead D dyadicRead →
            Cont dyadicRead R regularRead →
              Cont regularRead E sealRead →
                Cont sealRead L terminalRead →
                  PkgSig bundle terminalRead pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row terminalRead ∧
                          ∃ packet : CofinalModulusNormalizationSealUp,
                            packet =
                                CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N ∧
                              cofinalModulusNormalizationSealFields packet =
                                [A, B, M, W, D, R, E, H, C, P, L, N])
                      (fun row : BHist =>
                        Cont A B M ∧ Cont M W sharedRead ∧
                          Cont sharedRead D dyadicRead ∧ Cont dyadicRead R regularRead ∧
                            Cont regularRead E sealRead ∧ Cont sealRead L row)
                      (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldsExact routeAB routeShared routeDyadic routeRegular routeSeal routeTerminal pkgSig
  have sourceAtTerminal :
      hsame terminalRead terminalRead ∧
        ∃ packet : CofinalModulusNormalizationSealUp,
          packet = CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N ∧
            cofinalModulusNormalizationSealFields packet =
              [A, B, M, W, D, R, E, H, C, P, L, N] := by
    exact
      ⟨hsame_refl terminalRead,
        ⟨CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N, rfl,
          fieldsExact⟩⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceAtTerminal
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨routeAB, routeShared, routeDyadic, routeRegular, routeSeal,
          cont_result_hsame_transport routeTerminal (hsame_symm source.left)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

theorem CofinalModulusNormalizationSeal_classifier_stability
    {A B M W D R E H C P L N A' B' M' W' D' R' E' H' C' P' L' N' sharedRead
      sharedRead' dyadicRead dyadicRead' regularRead regularRead' sealRead sealRead'
      terminalRead terminalRead' : BHist} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] ->
      cofinalModulusNormalizationSealFields
          (CofinalModulusNormalizationSealUp.mk A' B' M' W' D' R' E' H' C' P' L' N') =
        [A', B', M', W', D', R', E', H', C', P', L', N'] ->
        hsame A A' -> hsame B B' -> hsame M M' -> hsame W W' -> hsame D D' ->
          hsame R R' -> hsame E E' -> hsame L L' -> Cont A B M -> Cont A' B' M' ->
            Cont M W sharedRead -> Cont M' W' sharedRead' ->
              Cont sharedRead D dyadicRead -> Cont sharedRead' D' dyadicRead' ->
                Cont dyadicRead R regularRead -> Cont dyadicRead' R' regularRead' ->
                  Cont regularRead E sealRead -> Cont regularRead' E' sealRead' ->
                    Cont sealRead L terminalRead -> Cont sealRead' L' terminalRead' ->
                      hsame sharedRead sharedRead' ∧ hsame dyadicRead dyadicRead' ∧
                        hsame regularRead regularRead' ∧ hsame sealRead sealRead' ∧
                          hsame terminalRead terminalRead' := by
  -- BEDC touchpoint anchor: BHist hsame Cont CofinalModulusNormalizationSealUp
  intro _fieldsExact _fieldsExact' sameA sameB sameM sameW sameD sameR sameE sameL
    routeAB routeAB' routeShared routeShared' routeDyadic routeDyadic' routeRegular
    routeRegular' routeSeal routeSeal' routeTerminal routeTerminal'
  have sameMFromSchedules : hsame M M' :=
    cont_respects_hsame sameA sameB routeAB routeAB'
  have sameMStable : hsame M M' :=
    hsame_trans sameMFromSchedules (hsame_trans (hsame_symm sameM) sameM)
  have sameShared : hsame sharedRead sharedRead' :=
    cont_respects_hsame sameMStable sameW routeShared routeShared'
  have sameDyadic : hsame dyadicRead dyadicRead' :=
    cont_respects_hsame sameShared sameD routeDyadic routeDyadic'
  have sameRegular : hsame regularRead regularRead' :=
    cont_respects_hsame sameDyadic sameR routeRegular routeRegular'
  have sameSeal : hsame sealRead sealRead' :=
    cont_respects_hsame sameRegular sameE routeSeal routeSeal'
  have sameTerminal : hsame terminalRead terminalRead' :=
    cont_respects_hsame sameSeal sameL routeTerminal routeTerminal'
  exact ⟨sameShared, sameDyadic, sameRegular, sameSeal, sameTerminal⟩

end BEDC.Derived.CofinalModulusNormalizationSealUp
