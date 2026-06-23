import BEDC.Derived.RegularCauchyWindowFusionUp.PublicExport

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionScopedRowExhaustion [AskSetup] [PackageSetup]
    {R W S D E H C P N tailRead budgetRead sealRead publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              UnaryHistory H →
                Cont W S tailRead →
                  Cont S D budgetRead →
                    Cont tailRead budgetRead sealRead →
                      Cont H sealRead publicRead →
                        Cont H sealRead publicRead' →
                          PkgSig bundle P pkg →
                            PkgSig bundle publicRead pkg →
                              hsame publicRead publicRead' ∧
                                UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                                    PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro _rUnary wUnary sUnary dUnary _eUnary hUnary tailRoute budgetRoute sealRoute
    publicRoute publicRoute' provenancePkg _publicPkg
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sUnary dUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary budgetUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary sealUnary publicRoute
  have samePublic : hsame publicRead publicRead' :=
    cont_deterministic publicRoute publicRoute'
  exact ⟨samePublic, tailUnary, budgetUnary, sealUnary, publicUnary, provenancePkg⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
