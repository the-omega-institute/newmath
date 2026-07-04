import BEDC.Derived.CompactMetricLocatedNetSelectionUp
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricLocatedNetSelectionUp

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

private def compactMetricLocatedNetSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricLocatedNetSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricLocatedNetSelectionEncodeBHist h

private def compactMetricLocatedNetSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricLocatedNetSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricLocatedNetSelectionDecodeBHist tail)

private theorem compactMetricLocatedNetSelection_decode_encode_bhist :
    ∀ h : BHist,
      compactMetricLocatedNetSelectionDecodeBHist
        (compactMetricLocatedNetSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def compactMetricLocatedNetSelectionToEventFlow :
    CompactMetricLocatedNetSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactMetricLocatedNetSelectionFields x).map
      compactMetricLocatedNetSelectionEncodeBHist

private def compactMetricLocatedNetSelectionFromEventFlow :
    EventFlow → Option CompactMetricLocatedNetSelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
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
                                            (CompactMetricLocatedNetSelectionUp.mk
                                              (compactMetricLocatedNetSelectionDecodeBHist K)
                                              (compactMetricLocatedNetSelectionDecodeBHist D)
                                              (compactMetricLocatedNetSelectionDecodeBHist W)
                                              (compactMetricLocatedNetSelectionDecodeBHist R)
                                              (compactMetricLocatedNetSelectionDecodeBHist E)
                                              (compactMetricLocatedNetSelectionDecodeBHist H)
                                              (compactMetricLocatedNetSelectionDecodeBHist C)
                                              (compactMetricLocatedNetSelectionDecodeBHist P)
                                              (compactMetricLocatedNetSelectionDecodeBHist N))
                                      | _ :: _ => none

private theorem compactMetricLocatedNetSelection_mk_congr
    {K K' D D' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hK : K' = K)
    (hD : D' = D)
    (hW : W' = W)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    CompactMetricLocatedNetSelectionUp.mk K' D' W' R' E' H' C' P' N' =
      CompactMetricLocatedNetSelectionUp.mk K D W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem compactMetricLocatedNetSelection_round_trip :
    ∀ x : CompactMetricLocatedNetSelectionUp,
      compactMetricLocatedNetSelectionFromEventFlow
        (compactMetricLocatedNetSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K D W R E H C P N =>
      change
        some
          (CompactMetricLocatedNetSelectionUp.mk
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist K))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist D))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist W))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist R))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist E))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist H))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist C))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist P))
            (compactMetricLocatedNetSelectionDecodeBHist
              (compactMetricLocatedNetSelectionEncodeBHist N))) =
          some (CompactMetricLocatedNetSelectionUp.mk K D W R E H C P N)
      exact
        congrArg some
          (compactMetricLocatedNetSelection_mk_congr
            (compactMetricLocatedNetSelection_decode_encode_bhist K)
            (compactMetricLocatedNetSelection_decode_encode_bhist D)
            (compactMetricLocatedNetSelection_decode_encode_bhist W)
            (compactMetricLocatedNetSelection_decode_encode_bhist R)
            (compactMetricLocatedNetSelection_decode_encode_bhist E)
            (compactMetricLocatedNetSelection_decode_encode_bhist H)
            (compactMetricLocatedNetSelection_decode_encode_bhist C)
            (compactMetricLocatedNetSelection_decode_encode_bhist P)
            (compactMetricLocatedNetSelection_decode_encode_bhist N))

private theorem compactMetricLocatedNetSelectionToEventFlow_injective
    {x y : CompactMetricLocatedNetSelectionUp} :
    compactMetricLocatedNetSelectionToEventFlow x =
      compactMetricLocatedNetSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricLocatedNetSelectionFromEventFlow
          (compactMetricLocatedNetSelectionToEventFlow x) =
        compactMetricLocatedNetSelectionFromEventFlow
          (compactMetricLocatedNetSelectionToEventFlow y) :=
    congrArg compactMetricLocatedNetSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactMetricLocatedNetSelection_round_trip x).symm
      (Eq.trans hread (compactMetricLocatedNetSelection_round_trip y)))

instance compactMetricLocatedNetSelectionBHistCarrier :
    BHistCarrier CompactMetricLocatedNetSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricLocatedNetSelectionToEventFlow
  fromEventFlow := compactMetricLocatedNetSelectionFromEventFlow

instance compactMetricLocatedNetSelectionChapterTasteGate :
    ChapterTasteGate CompactMetricLocatedNetSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := compactMetricLocatedNetSelection_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactMetricLocatedNetSelectionToEventFlow_injective heq)

theorem CompactMetricLocatedNetSelection_l10_handoff [AskSetup] [PackageSetup]
    {K D W R E H C P N locatedRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactMetricLocatedNetSelectionCarrier K D W R E H C P N bundle pkg →
      Cont K D W →
        Cont W R E →
          Cont E N locatedRead →
            Cont locatedRead E terminalRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨
                        hsame row E ∨ hsame row N ∨ hsame row locatedRead ∨
                          hsame row terminalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K D W ∧ Cont W R E ∧
                        Cont E N locatedRead ∧ Cont locatedRead E terminalRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧ UnaryHistory locatedRead ∧ UnaryHistory terminalRead ∧
                      compactMetricLocatedNetSelectionFields
                        (CompactMetricLocatedNetSelectionUp.mk K D W R E H C P N) =
                          [K, D, W, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactDyadicRoute windowReadbackRoute locatedRoute terminalRoute
    provenancePkg namePkg
  obtain ⟨_kUnary, _dUnary, _wUnary, _rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, fieldsExact, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed eUnary nUnary locatedRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed locatedUnary eUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row N ∨ hsame row locatedRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K D W ∧ Cont W R E ∧ Cont E N locatedRead ∧
              Cont locatedRead E terminalRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactDyadicRoute, windowReadbackRoute, locatedRoute,
          terminalRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, locatedUnary, terminalUnary, fieldsExact⟩

end BEDC.Derived.CompactMetricLocatedNetSelectionUp
