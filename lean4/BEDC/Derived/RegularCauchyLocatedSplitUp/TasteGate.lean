import BEDC.Derived.RegularCauchyLocatedSplitUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedSplitUp

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

def regularCauchyLocatedSplitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedSplitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedSplitEncodeBHist h

def regularCauchyLocatedSplitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedSplitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedSplitDecodeBHist tail)

private theorem regularCauchyLocatedSplitDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyLocatedSplitDecodeBHist
        (regularCauchyLocatedSplitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyLocatedSplitToEventFlow :
    BEDC.Derived.RegularCauchyLocatedSplitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.RegularCauchyLocatedSplitUp.mk Q L D W R E H C P N =>
      [regularCauchyLocatedSplitEncodeBHist Q,
        regularCauchyLocatedSplitEncodeBHist L,
        regularCauchyLocatedSplitEncodeBHist D,
        regularCauchyLocatedSplitEncodeBHist W,
        regularCauchyLocatedSplitEncodeBHist R,
        regularCauchyLocatedSplitEncodeBHist E,
        regularCauchyLocatedSplitEncodeBHist H,
        regularCauchyLocatedSplitEncodeBHist C,
        regularCauchyLocatedSplitEncodeBHist P,
        regularCauchyLocatedSplitEncodeBHist N]

def regularCauchyLocatedSplitFromEventFlow :
    EventFlow → Option BEDC.Derived.RegularCauchyLocatedSplitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (BEDC.Derived.RegularCauchyLocatedSplitUp.mk
                                                  (regularCauchyLocatedSplitDecodeBHist Q)
                                                  (regularCauchyLocatedSplitDecodeBHist L)
                                                  (regularCauchyLocatedSplitDecodeBHist D)
                                                  (regularCauchyLocatedSplitDecodeBHist W)
                                                  (regularCauchyLocatedSplitDecodeBHist R)
                                                  (regularCauchyLocatedSplitDecodeBHist E)
                                                  (regularCauchyLocatedSplitDecodeBHist H)
                                                  (regularCauchyLocatedSplitDecodeBHist C)
                                                  (regularCauchyLocatedSplitDecodeBHist P)
                                                  (regularCauchyLocatedSplitDecodeBHist N))
                                          | _ :: _ => none

private theorem regularCauchyLocatedSplit_mk_congr
    {Q Q' L L' D D' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q)
    (hL : L' = L)
    (hD : D' = D)
    (hW : W' = W)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    BEDC.Derived.RegularCauchyLocatedSplitUp.mk Q' L' D' W' R' E' H' C' P' N' =
      BEDC.Derived.RegularCauchyLocatedSplitUp.mk Q L D W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hL
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem regularCauchyLocatedSplit_round_trip :
    ∀ x : BEDC.Derived.RegularCauchyLocatedSplitUp,
      regularCauchyLocatedSplitFromEventFlow
        (regularCauchyLocatedSplitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q L D W R E H C P N =>
      change
        some
          (BEDC.Derived.RegularCauchyLocatedSplitUp.mk
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist Q))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist L))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist D))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist W))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist R))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist E))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist H))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist C))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist P))
            (regularCauchyLocatedSplitDecodeBHist
              (regularCauchyLocatedSplitEncodeBHist N))) =
          some (BEDC.Derived.RegularCauchyLocatedSplitUp.mk Q L D W R E H C P N)
      exact
        congrArg some
          (regularCauchyLocatedSplit_mk_congr
            (regularCauchyLocatedSplitDecode_encode_bhist Q)
            (regularCauchyLocatedSplitDecode_encode_bhist L)
            (regularCauchyLocatedSplitDecode_encode_bhist D)
            (regularCauchyLocatedSplitDecode_encode_bhist W)
            (regularCauchyLocatedSplitDecode_encode_bhist R)
            (regularCauchyLocatedSplitDecode_encode_bhist E)
            (regularCauchyLocatedSplitDecode_encode_bhist H)
            (regularCauchyLocatedSplitDecode_encode_bhist C)
            (regularCauchyLocatedSplitDecode_encode_bhist P)
            (regularCauchyLocatedSplitDecode_encode_bhist N))

private theorem regularCauchyLocatedSplitToEventFlow_injective
    {x y : BEDC.Derived.RegularCauchyLocatedSplitUp} :
    regularCauchyLocatedSplitToEventFlow x =
      regularCauchyLocatedSplitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedSplitFromEventFlow (regularCauchyLocatedSplitToEventFlow x) =
        regularCauchyLocatedSplitFromEventFlow (regularCauchyLocatedSplitToEventFlow y) :=
    congrArg regularCauchyLocatedSplitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (regularCauchyLocatedSplit_round_trip x).symm
      (Eq.trans hread (regularCauchyLocatedSplit_round_trip y)))

instance regularCauchyLocatedSplitBHistCarrier :
    BHistCarrier BEDC.Derived.RegularCauchyLocatedSplitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedSplitToEventFlow
  fromEventFlow := regularCauchyLocatedSplitFromEventFlow

instance regularCauchyLocatedSplitChapterTasteGate :
    ChapterTasteGate BEDC.Derived.RegularCauchyLocatedSplitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := regularCauchyLocatedSplit_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocatedSplitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.RegularCauchyLocatedSplitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocatedSplitChapterTasteGate

theorem RegularCauchyLocatedSplitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLocatedSplitDecodeBHist
        (regularCauchyLocatedSplitEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.RegularCauchyLocatedSplitUp,
        regularCauchyLocatedSplitFromEventFlow
          (regularCauchyLocatedSplitToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.RegularCauchyLocatedSplitUp,
          regularCauchyLocatedSplitToEventFlow x =
            regularCauchyLocatedSplitToEventFlow y → x = y) ∧
          regularCauchyLocatedSplitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyLocatedSplitDecode_encode_bhist, regularCauchyLocatedSplit_round_trip,
      (fun x y h =>
        regularCauchyLocatedSplitToEventFlow_injective (x := x) (y := y) h),
      rfl⟩

theorem RegularCauchyLocatedSplit_namecert_obligations [AskSetup] [PackageSetup]
    {Q L D W R E H C P N sourceLocated splitRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory L ->
        UnaryHistory D ->
          UnaryHistory W ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont Q L sourceLocated ->
                          Cont sourceLocated D splitRead ->
                            Cont splitRead R sealRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle sealRead pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row Q ∨ hsame row L ∨ hsame row D ∨
                                          hsame row W ∨ hsame row R ∨ hsame row E ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row N ∨ hsame row sourceLocated ∨
                                                hsame row splitRead ∨ hsame row sealRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont Q L sourceLocated ∧
                                          Cont sourceLocated D splitRead ∧
                                            Cont splitRead R sealRead ∧
                                              PkgSig bundle P pkg ∧
                                                PkgSig bundle sealRead pkg)
                                      hsame ∧
                                    UnaryHistory sourceLocated ∧ UnaryHistory splitRead ∧
                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryQ unaryL unaryD _unaryW unaryR _unaryE _unaryH _unaryC _unaryP _unaryN
    sourceRoute splitRoute sealRoute pkgP sealPkg
  have sourceUnary : UnaryHistory sourceLocated :=
    unary_cont_closed unaryQ unaryL sourceRoute
  have splitUnary : UnaryHistory splitRead :=
    unary_cont_closed sourceUnary unaryD splitRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed splitUnary unaryR sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row L ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row sourceLocated ∨
                  hsame row splitRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q L sourceLocated ∧ Cont sourceLocated D splitRead ∧
              Cont splitRead R sealRead ∧ PkgSig bundle P pkg ∧
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
                            (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, splitRoute, sealRoute, pkgP, sealPkg⟩
  }
  exact ⟨cert, sourceUnary, splitUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyLocatedSplitUp
