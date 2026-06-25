import BEDC.Derived.BornologyUp.ObligationClosureRoute

namespace BEDC.Derived.BornologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BornologyScopeKernelGrounding [AskSetup] [PackageSetup]
    {F S U E D H C P N sourceRead heredityRead unionRead cauchyRead namedRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BornologyTasteGate_single_carrier_alignment_fields (BornologyUp.mk F S U E D H C P N) =
        [F, S, U, E, D, H, C, P, N] →
      Cont F E sourceRead →
        Cont sourceRead S heredityRead →
          Cont heredityRead U unionRead →
            Cont unionRead D cauchyRead →
              Cont cauchyRead N namedRead →
                Cont namedRead H scopedRead →
                  UnaryHistory F →
                    UnaryHistory E →
                      UnaryHistory S →
                        UnaryHistory U →
                          UnaryHistory D →
                            UnaryHistory H →
                              UnaryHistory C →
                                UnaryHistory P →
                                  UnaryHistory N →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle scopedRead pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row scopedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row F ∨ hsame row S ∨ hsame row U ∨
                                                hsame row E ∨ hsame row D ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                    hsame row scopedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont F E sourceRead ∧
                                                Cont sourceRead S heredityRead ∧
                                                  Cont heredityRead U unionRead ∧
                                                    Cont unionRead D cauchyRead ∧
                                                      Cont cauchyRead N namedRead ∧
                                                        Cont namedRead H scopedRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle scopedRead pkg)
                                            hsame ∧
                                          UnaryHistory sourceRead ∧
                                            UnaryHistory heredityRead ∧
                                              UnaryHistory unionRead ∧
                                                UnaryHistory cauchyRead ∧
                                                  UnaryHistory namedRead ∧
                                                    UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldRows sourceRoute heredityRoute unionRoute cauchyRoute nameRoute scopedRoute fUnary
    eUnary sUnary uUnary dUnary hUnary cUnary pUnary nUnary provenancePkg scopedPkg
  cases fieldRows
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed fUnary eUnary sourceRoute
  have heredityUnary : UnaryHistory heredityRead :=
    unary_cont_closed sourceUnary sUnary heredityRoute
  have unionUnary : UnaryHistory unionRead :=
    unary_cont_closed heredityUnary uUnary unionRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed unionUnary dUnary cauchyRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed cauchyUnary nUnary nameRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed namedUnary hUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F E sourceRead ∧ Cont sourceRead S heredityRead ∧
              Cont heredityRead U unionRead ∧ Cont unionRead D cauchyRead ∧
                Cont cauchyRead N namedRead ∧ Cont namedRead H scopedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle scopedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
        equiv_refl := by
          intro row source
          exact hsame_refl row
        equiv_symm := by
          intro row k sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro row k r sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row k sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))
      ledger_sound := by
        intro row source
        exact
          ⟨source.right, sourceRoute, heredityRoute, unionRoute, cauchyRoute, nameRoute,
            scopedRoute, provenancePkg, scopedPkg⟩
    }
  exact
    ⟨cert, sourceUnary, heredityUnary, unionUnary, cauchyUnary, namedUnary, scopedUnary⟩

end BEDC.Derived.BornologyUp
