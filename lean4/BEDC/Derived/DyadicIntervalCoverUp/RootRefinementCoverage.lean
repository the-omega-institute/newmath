import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootRefinementCoverage [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N Lp Up Mp Rp Vp Wp Qp Ap Hp Cp Pp Np endpointRead
      coverRead sealRead transportedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      DyadicIntervalCoverRootObligationSurface Lp Up Mp Rp Vp Wp Qp Ap Hp Cp Pp Np
        bundle pkg →
        hsame L Lp →
          hsame U Up →
            hsame M Mp →
              hsame R Rp →
                hsame V Vp →
                  Cont L U endpointRead →
                    Cont M R coverRead →
                      Cont coverRead A sealRead →
                        Cont sealRead Hp transportedRead →
                          Cont transportedRead Np namedRead →
                            PkgSig bundle namedRead pkg →
                              SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row L ∨ hsame row U ∨ hsame row M ∨
                                        hsame row R ∨ hsame row V ∨ hsame row Lp ∨
                                          hsame row Up ∨ hsame row Mp ∨ hsame row Rp ∨
                                            hsame row Vp ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont L U endpointRead ∧
                                        Cont M R coverRead ∧ Cont coverRead A sealRead ∧
                                          Cont sealRead Hp transportedRead ∧
                                            Cont transportedRead Np namedRead ∧
                                              PkgSig bundle namedRead pkg)
                                    hsame ∧
                                  UnaryHistory endpointRead ∧ UnaryHistory coverRead ∧
                                    UnaryHistory sealRead ∧ UnaryHistory transportedRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro surface surface' _sameL _sameU _sameM _sameR _sameV endpointRoute coverRoute
    sealRoute transportedRoute namedRoute namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have hpUnary : UnaryHistory Hp :=
    surface'.right.right.right.right.right.right.right.right.left
  have npUnary : UnaryHistory Np :=
    surface'.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed sealUnary hpUnary transportedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed transportedUnary npUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row Lp ∨ hsame row Up ∨ hsame row Mp ∨ hsame row Rp ∨
                hsame row Vp ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont M R coverRead ∧
              Cont coverRead A sealRead ∧ Cont sealRead Hp transportedRead ∧
                Cont transportedRead Np namedRead ∧ PkgSig bundle namedRead pkg)
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
        ⟨source.right, endpointRoute, coverRoute, sealRoute, transportedRoute, namedRoute,
          namedPkg⟩
  }
  exact
    ⟨cert, endpointUnary, coverUnary, sealUnary, transportedUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
