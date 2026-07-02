import BEDC.Derived.StepIndexedTotalHostUp

namespace BEDC.Derived.StepIndexedTotalHostUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StepIndexedTotalHostCarrier_sibling_boundary [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert sibling :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      UnaryHistory sibling →
        Cont trace bounded sibling →
          UnaryHistory trace ∧ UnaryHistory bounded ∧ UnaryHistory sibling ∧
            Cont trace bounded sibling ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier siblingUnary siblingRoute
  exact
    ⟨carrier.trace_unary, carrier.bounded_unary, siblingUnary, siblingRoute,
      carrier.provenance_pkg⟩

theorem StepIndexedTotalHostCarrier_public_sibling_boundary [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert boundaryRead
      namedRead publicRead sibling : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      Cont normal refusal boundaryRead →
        Cont boundaryRead nameCert namedRead →
          Cont namedRead route publicRead →
            Cont publicRead bounded sibling →
              PkgSig bundle namedRead pkg →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row host ∨ hsame row fuel ∨ hsame row trace ∨
                          hsame row normal ∨ hsame row bounded ∨ hsame row refusal ∨
                            hsame row transport ∨ hsame row route ∨
                              hsame row boundaryRead ∨ hsame row namedRead ∨
                                hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont host fuel trace ∧
                          Cont trace bounded normal ∧ Cont refusal transport route ∧
                            Cont normal refusal boundaryRead ∧
                              Cont boundaryRead nameCert namedRead ∧
                                Cont namedRead route publicRead ∧
                                  PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory publicRead ∧ UnaryHistory bounded ∧
                      UnaryHistory sibling ∧ Cont publicRead bounded sibling ∧
                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier SemanticNameCert BHist Cont PkgSig UnaryHistory
  intro carrier boundaryRoute namedRoute publicRoute siblingRoute namedPkg publicPkg
  have publicResult :=
    StepIndexedTotalHostCarrier_public_interface carrier boundaryRoute namedRoute publicRoute
      namedPkg publicPkg
  have siblingUnary : UnaryHistory sibling :=
    unary_cont_closed publicResult.right carrier.bounded_unary siblingRoute
  exact
    ⟨publicResult.left, publicResult.right, carrier.bounded_unary, siblingUnary,
      siblingRoute, publicPkg⟩

end BEDC.Derived.StepIndexedTotalHostUp
