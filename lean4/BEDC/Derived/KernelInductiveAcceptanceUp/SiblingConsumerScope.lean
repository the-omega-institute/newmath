import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_sibling_consumer_scope [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance nameCert
      signatureRead eliminatorRead refusalRead subjectRead siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures signatureRead →
      Cont signatures eliminators eliminatorRead →
        Cont positivity recursion refusalRead →
          Cont eliminators recursion subjectRead →
            Cont subjectRead routes siblingRead →
              PkgSig bundle siblingRead pkg →
                UnaryHistory declaration →
                  UnaryHistory signatures →
                    UnaryHistory eliminators →
                      UnaryHistory positivity →
                        UnaryHistory recursion →
                          UnaryHistory routes →
                            UnaryHistory signatureRead ∧ UnaryHistory eliminatorRead ∧
                              UnaryHistory refusalRead ∧ UnaryHistory subjectRead ∧
                                UnaryHistory siblingRead ∧ Cont subjectRead routes siblingRead ∧
                                  PkgSig bundle siblingRead pkg ∧
                                    List.Mem
                                      (kernelInductiveAcceptanceEncodeBHist signatures)
                                      (kernelInductiveAcceptanceToEventFlow
                                        (KernelInductiveAcceptanceUp.mk declaration signatures
                                          eliminators positivity recursion transport routes
                                          provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg UnaryHistory
  intro declarationSignaturesRead signaturesEliminatorsRead positivityRecursionRead
    eliminatorsRecursionRead subjectRoutesRead siblingPkg declarationUnary signaturesUnary
    eliminatorsUnary positivityUnary recursionUnary routesUnary
  have signatureUnary : UnaryHistory signatureRead :=
    unary_cont_closed declarationUnary signaturesUnary declarationSignaturesRead
  have eliminatorUnary : UnaryHistory eliminatorRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary signaturesEliminatorsRead
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed positivityUnary recursionUnary positivityRecursionRead
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionRead
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed subjectUnary routesUnary subjectRoutesRead
  have signaturesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
            recursion transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist routes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist nameCert]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
  exact
    ⟨signatureUnary, eliminatorUnary, refusalUnary, subjectUnary, siblingUnary,
      subjectRoutesRead, siblingPkg, signaturesListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
