import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailGluingUp

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

inductive CauchyTailGluingUp : Type where
  | mk (X Y S T n D B Q R E H C P N : BHist) : CauchyTailGluingUp
  deriving DecidableEq

def cauchyTailGluingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailGluingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailGluingEncodeBHist h

def cauchyTailGluingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailGluingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailGluingDecodeBHist tail)

private theorem cauchyTailGluing_decode_encode_bhist :
    ∀ h : BHist, cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailGluingFields : CauchyTailGluingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailGluingUp.mk X Y S T n D B Q R E H C P N =>
      [X, Y, S, T, n, D, B, Q, R, E, H, C, P, N]

private theorem cauchyTailGluing_mk_congr
    {X X' Y Y' S S' T T' n n' D D' B B' Q Q' R R' E E' H H' C C' P P' N N' :
      BHist}
    (hX : X' = X) (hY : Y' = Y) (hS : S' = S) (hT : T' = T) (hn : n' = n)
    (hD : D' = D) (hB : B' = B) (hQ : Q' = Q) (hR : R' = R) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyTailGluingUp.mk X' Y' S' T' n' D' B' Q' R' E' H' C' P' N' =
      CauchyTailGluingUp.mk X Y S T n D B Q R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hS
  cases hT
  cases hn
  cases hD
  cases hB
  cases hQ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyTailGluingToEventFlow : CauchyTailGluingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailGluingFields x).map cauchyTailGluingEncodeBHist

def cauchyTailGluingFromEventFlow : EventFlow → Option CauchyTailGluingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | Y :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | n :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | B :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | R :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | H :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | P :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (CauchyTailGluingUp.mk
                                                                  (cauchyTailGluingDecodeBHist X)
                                                                  (cauchyTailGluingDecodeBHist Y)
                                                                  (cauchyTailGluingDecodeBHist S)
                                                                  (cauchyTailGluingDecodeBHist T)
                                                                  (cauchyTailGluingDecodeBHist n)
                                                                  (cauchyTailGluingDecodeBHist D)
                                                                  (cauchyTailGluingDecodeBHist B)
                                                                  (cauchyTailGluingDecodeBHist Q)
                                                                  (cauchyTailGluingDecodeBHist R)
                                                                  (cauchyTailGluingDecodeBHist E)
                                                                  (cauchyTailGluingDecodeBHist H)
                                                                  (cauchyTailGluingDecodeBHist C)
                                                                  (cauchyTailGluingDecodeBHist P)
                                                                  (cauchyTailGluingDecodeBHist N))
                                                          | _ :: _ => none

private theorem cauchyTailGluing_round_trip :
    ∀ x : CauchyTailGluingUp,
      cauchyTailGluingFromEventFlow (cauchyTailGluingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S T n D B Q R E H C P N =>
      change
        some
          (CauchyTailGluingUp.mk
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist X))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist Y))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist S))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist T))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist n))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist D))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist B))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist Q))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist R))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist E))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist H))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist C))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist P))
            (cauchyTailGluingDecodeBHist (cauchyTailGluingEncodeBHist N))) =
          some (CauchyTailGluingUp.mk X Y S T n D B Q R E H C P N)
      exact
        congrArg some
          (cauchyTailGluing_mk_congr
            (cauchyTailGluing_decode_encode_bhist X)
            (cauchyTailGluing_decode_encode_bhist Y)
            (cauchyTailGluing_decode_encode_bhist S)
            (cauchyTailGluing_decode_encode_bhist T)
            (cauchyTailGluing_decode_encode_bhist n)
            (cauchyTailGluing_decode_encode_bhist D)
            (cauchyTailGluing_decode_encode_bhist B)
            (cauchyTailGluing_decode_encode_bhist Q)
            (cauchyTailGluing_decode_encode_bhist R)
            (cauchyTailGluing_decode_encode_bhist E)
            (cauchyTailGluing_decode_encode_bhist H)
            (cauchyTailGluing_decode_encode_bhist C)
            (cauchyTailGluing_decode_encode_bhist P)
            (cauchyTailGluing_decode_encode_bhist N))

private theorem cauchyTailGluingToEventFlow_injective {x y : CauchyTailGluingUp} :
    cauchyTailGluingToEventFlow x = cauchyTailGluingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailGluingFromEventFlow (cauchyTailGluingToEventFlow x) =
        cauchyTailGluingFromEventFlow (cauchyTailGluingToEventFlow y) :=
    congrArg cauchyTailGluingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailGluing_round_trip x).symm
      (Eq.trans hread (cauchyTailGluing_round_trip y)))

instance cauchyTailGluingBHistCarrier : BHistCarrier CauchyTailGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailGluingToEventFlow
  fromEventFlow := cauchyTailGluingFromEventFlow

instance cauchyTailGluingChapterTasteGate : ChapterTasteGate CauchyTailGluingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailGluingFromEventFlow (cauchyTailGluingToEventFlow x) = some x
    exact cauchyTailGluing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailGluingToEventFlow_injective heq)

def CauchyTailGluingCarrier (X Y S T n D B Q R E H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory S ∧ UnaryHistory T ∧
    UnaryHistory n ∧ UnaryHistory D ∧ UnaryHistory B ∧ UnaryHistory Q ∧
      UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ Cont Q R E

theorem CauchyTailGluingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y S T n D B Q R E H C P N realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailGluingCarrier X Y S T n D B Q R E H C P N →
      Cont Q R E →
        Cont E H realRead →
          PkgSig bundle realRead pkg →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row T ∨
                      hsame row n ∨ hsame row D ∨ hsame row B ∨ hsame row Q ∨
                        hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row realRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Q R E ∧ Cont E H realRead ∧
                      PkgSig bundle realRead pkg ∧ PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier classifierRoute sealRoute readPkg provenancePkg
  obtain ⟨_leftUnary, _rightUnary, _leftWindowUnary, _rightWindowUnary, _indexUnary,
    _dyadicUnary, _ballUnary, _classifierUnary, _gluedUnary, sealUnary, transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _carrierClassifierRoute⟩ := carrier
  have readUnary : UnaryHistory realRead :=
    unary_cont_closed sealUnary transportUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row S ∨ hsame row T ∨ hsame row n ∨
              hsame row D ∨ hsame row B ∨ hsame row Q ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q R E ∧ Cont E H realRead ∧
              PkgSig bundle realRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, readUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro row row' same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
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
                                (Or.inr (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, sealRoute, readPkg, provenancePkg⟩
  }
  exact ⟨cert, readUnary⟩

end BEDC.Derived.CauchyTailGluingUp
