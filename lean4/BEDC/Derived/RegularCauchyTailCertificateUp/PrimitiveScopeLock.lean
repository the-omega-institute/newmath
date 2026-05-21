import BEDC.Derived.RegularCauchyTailCertificateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyTailCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem RegularCauchyTailCertificate_primitive_scope_lock [AskSetup] [PackageSetup]
    {X W R D E H C P N XW WR RD DE support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyTailCertificateFields (RegularCauchyTailCertificateUp.mk X W R D E H C P N) =
        [X, W, R, D, E, H, C, P, N] ->
      Cont X W XW ->
        Cont XW R WR ->
          Cont WR D RD ->
            Cont RD E DE ->
              Cont H C support ->
                UnaryHistory X ->
                  UnaryHistory W ->
                    UnaryHistory R ->
                      UnaryHistory D ->
                        UnaryHistory E ->
                          UnaryHistory H ->
                            UnaryHistory C ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row support ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row support ∧ Cont X W XW ∧ Cont XW R WR ∧
                                        Cont WR D RD ∧ Cont RD E DE ∧ Cont H C support)
                                    (fun row : BHist =>
                                      hsame row support ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory XW ∧ UnaryHistory WR ∧ UnaryHistory RD ∧
                                    UnaryHistory DE ∧ UnaryHistory support := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fields sourceWindow windowReadback readbackDyadic dyadicReal supportRoute
    sourceUnary windowUnary readbackUnary dyadicUnary realUnary transportUnary replayUnary
    namePkg
  have _fields :
      regularCauchyTailCertificateFields
          (RegularCauchyTailCertificateUp.mk X W R D E H C P N) =
        [X, W, R, D, E, H, C, P, N] := fields
  have xwUnary : UnaryHistory XW :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have wrUnary : UnaryHistory WR :=
    unary_cont_closed xwUnary readbackUnary windowReadback
  have rdUnary : UnaryHistory RD :=
    unary_cont_closed wrUnary dyadicUnary readbackDyadic
  have deUnary : UnaryHistory DE :=
    unary_cont_closed rdUnary realUnary dyadicReal
  have supportUnary : UnaryHistory support :=
    unary_cont_closed transportUnary replayUnary supportRoute
  have sourceAtSupport : hsame support support ∧ UnaryHistory support :=
    ⟨hsame_refl support, supportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row support ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row support ∧ Cont X W XW ∧ Cont XW R WR ∧ Cont WR D RD ∧
              Cont RD E DE ∧ Cont H C support)
          (fun row : BHist => hsame row support ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro support sourceAtSupport
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
        ⟨source.left, sourceWindow, windowReadback, readbackDyadic, dyadicReal,
          supportRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, xwUnary, wrUnary, rdUnary, deUnary, supportUnary⟩

end BEDC.Derived.RegularCauchyTailCertificateUp
