import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootSubstitutionRouteExactness [AskSetup] [PackageSetup]
    {T V d Csrc Cval Q R L A H C P N substRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Csrc ->
      UnaryHistory Cval ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory A ->
              Cont Csrc Cval Q ->
                Cont Q R substRead ->
                  Cont substRead A auditRead ->
                    PkgSig bundle auditRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row T ∨ hsame row V ∨ hsame row d ∨ hsame row Csrc ∨
                              hsame row Cval ∨ hsame row Q ∨ hsame row R ∨ hsame row L ∨
                                hsame row A ∨ Cont substRead A auditRead)
                          (fun row : BHist =>
                            PkgSig bundle auditRead pkg ∧ hsame row auditRead)
                          hsame ∧
                        UnaryHistory substRead ∧ UnaryHistory auditRead ∧
                          Cont Csrc Cval Q ∧ Cont Q R substRead ∧
                            Cont substRead A auditRead ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _csrcUnary _cvalUnary qUnary rUnary aUnary csrcCvalQ qRSubst substAudit auditPkg
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed qUnary rUnary qRSubst
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed substUnary aUnary substAudit
  have sourceAudit : hsame auditRead auditRead ∧ UnaryHistory auditRead :=
    ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row V ∨ hsame row d ∨ hsame row Csrc ∨
              hsame row Cval ∨ hsame row Q ∨ hsame row R ∨ hsame row L ∨
                hsame row A ∨ Cont substRead A auditRead)
          (fun row : BHist => PkgSig bundle auditRead pkg ∧ hsame row auditRead)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?carrier_inhabited
            equiv_refl := ?equiv_refl
            equiv_symm := ?equiv_symm
            equiv_trans := ?equiv_trans
            carrier_respects_equiv := ?carrier_respects_equiv }
        pattern_sound := ?pattern_sound
        ledger_sound := ?ledger_sound }
    · exact Exists.intro auditRead sourceAudit
    · intro row _source
      exact hsame_refl row
    · intro _row _target same
      exact hsame_symm same
    · intro _row _target _next sameRowTarget sameTargetNext
      exact hsame_trans sameRowTarget sameTargetNext
    · intro _row _target same source
      cases same
      exact source
    · intro _row _source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr substAudit))))))))
    · intro _row source
      exact ⟨auditPkg, source.left⟩
  exact ⟨cert, substUnary, auditUnary, csrcCvalQ, qRSubst, substAudit, auditPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
