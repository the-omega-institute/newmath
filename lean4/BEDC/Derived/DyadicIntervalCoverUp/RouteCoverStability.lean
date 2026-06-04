import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRouteCoverStability [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N Lp Up Mp Rp Vp Wp Qp Ap Hp Cp Pp Np endpointRead
      windowRead coverRead sealRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      DyadicIntervalCoverRootObligationSurface Lp Up Mp Rp Vp Wp Qp Ap Hp Cp Pp Np
        bundle pkg →
        hsame L Lp →
          hsame U Up →
            hsame M Mp →
              hsame R Rp →
                hsame V Vp →
                  hsame W Wp →
                    hsame Q Qp →
                      hsame A Ap →
                        Cont L U endpointRead →
                          Cont W Q windowRead →
                            Cont M R coverRead →
                              Cont coverRead A sealRead →
                                Cont sealRead Hp transportedRead →
                                  PkgSig bundle transportedRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row transportedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row L ∨ hsame row U ∨ hsame row M ∨
                                            hsame row R ∨ hsame row V ∨ hsame row W ∨
                                              hsame row Q ∨ hsame row A ∨ hsame row Lp ∨
                                                hsame row Up ∨ hsame row Mp ∨
                                                  hsame row Rp ∨ hsame row Vp ∨
                                                    hsame row Wp ∨ hsame row Qp ∨
                                                      hsame row Ap ∨
                                                        hsame row endpointRead ∨
                                                          hsame row windowRead ∨
                                                            hsame row coverRead ∨
                                                              hsame row sealRead ∨
                                                                hsame row transportedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont L U endpointRead ∧
                                            Cont W Q windowRead ∧ Cont M R coverRead ∧
                                              Cont coverRead A sealRead ∧
                                                Cont sealRead Hp transportedRead ∧
                                                  PkgSig bundle transportedRead pkg)
                                        hsame ∧
                                      UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                                        UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                                          UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro surface surface' _sameL _sameU sameM sameR _sameV _sameW _sameQ _sameA
    endpointRoute windowRoute coverRoute sealRoute transportedRoute transportedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have hpUnary : UnaryHistory Hp :=
    surface'.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed sealUnary hpUnary transportedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row Lp ∨ hsame row Up ∨
                hsame row Mp ∨ hsame row Rp ∨ hsame row Vp ∨ hsame row Wp ∨
                  hsame row Qp ∨ hsame row Ap ∨ hsame row endpointRead ∨
                    hsame row windowRead ∨ hsame row coverRead ∨ hsame row sealRead ∨
                      hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont M R coverRead ∧ Cont coverRead A sealRead ∧
                Cont sealRead Hp transportedRead ∧ PkgSig bundle transportedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedRead ⟨hsame_refl transportedRead, transportedUnary⟩
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
      right
      right
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
        ⟨source.right, endpointRoute, windowRoute, coverRoute, sealRoute, transportedRoute,
          transportedPkg⟩
  }
  exact ⟨cert, endpointUnary, windowUnary, coverUnary, sealUnary, transportedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
