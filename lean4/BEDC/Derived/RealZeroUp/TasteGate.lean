import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealZeroUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealZeroNameCertObligations [AskSetup] [PackageSetup]
    {q S Z0 D R H C P N sourceRead dyadicRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q →
      UnaryHistory S →
        UnaryHistory Z0 →
          UnaryHistory D →
            UnaryHistory R →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont q S sourceRead →
                        Cont sourceRead Z0 dyadicRead →
                          Cont dyadicRead D sealRead →
                            Cont sealRead R publicRead →
                              PkgSig bundle publicRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row q ∨ hsame row S ∨ hsame row Z0 ∨
                                        hsame row D ∨ hsame row R ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                                            hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont q S sourceRead ∧
                                        Cont sourceRead Z0 dyadicRead ∧
                                          Cont dyadicRead D sealRead ∧
                                            Cont sealRead R publicRead ∧
                                              PkgSig bundle publicRead pkg)
                                    hsame ∧
                                  UnaryHistory sourceRead ∧ UnaryHistory dyadicRead ∧
                                    UnaryHistory sealRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro qUnary sUnary zUnary dUnary rUnary _hUnary _cUnary _pUnary _nUnary sourceRoute
    dyadicRoute sealRoute publicRoute publicPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed qUnary sUnary sourceRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed sourceUnary zUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary dUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary rUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S sourceRead ∧ Cont sourceRead Z0 dyadicRead ∧
              Cont dyadicRead D sealRead ∧ Cont sealRead R publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
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
      right
      right
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
        ⟨source.right, sourceRoute, dyadicRoute, sealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, sourceUnary, dyadicUnary, sealUnary, publicUnary⟩

end BEDC.Derived.RealZeroUp
