import BEDC.Derived.BornologyUp.ScopeKernelGrounding

namespace BEDC.Derived.BornologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BornologyPublicBoundedFamilyExport [AskSetup] [PackageSetup]
    {F S U E D H C P N sourceRead heredityRead unionRead cauchyRead namedRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont F E sourceRead →
      Cont sourceRead S heredityRead →
        Cont heredityRead U unionRead →
          Cont unionRead D cauchyRead →
            Cont cauchyRead N namedRead →
              Cont namedRead P publicRead →
                UnaryHistory F →
                  UnaryHistory E →
                    UnaryHistory S →
                      UnaryHistory U →
                        UnaryHistory D →
                          UnaryHistory N →
                            UnaryHistory P →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row publicRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row F ∨ hsame row S ∨ hsame row U ∨
                                          hsame row E ∨ hsame row D ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row publicRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont F E sourceRead ∧
                                          Cont sourceRead S heredityRead ∧
                                            Cont heredityRead U unionRead ∧
                                              Cont unionRead D cauchyRead ∧
                                                Cont cauchyRead N namedRead ∧
                                                  Cont namedRead P publicRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory sourceRead ∧
                                      UnaryHistory heredityRead ∧
                                        UnaryHistory unionRead ∧
                                          UnaryHistory cauchyRead ∧
                                            UnaryHistory namedRead ∧
                                              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceRoute heredityRoute unionRoute cauchyRoute nameRoute publicRoute fUnary eUnary
    sUnary uUnary dUnary nUnary pUnary provenancePkg namePkg
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
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary pUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F E sourceRead ∧ Cont sourceRead S heredityRead ∧
              Cont heredityRead U unionRead ∧ Cont unionRead D cauchyRead ∧
                Cont cauchyRead N namedRead ∧ Cont namedRead P publicRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                          (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, sourceRoute, heredityRoute, unionRoute, cauchyRoute, nameRoute,
            publicRoute, provenancePkg, namePkg⟩
    }
  exact
    ⟨cert, sourceUnary, heredityUnary, unionUnary, cauchyUnary, namedUnary, publicUnary⟩

end BEDC.Derived.BornologyUp
