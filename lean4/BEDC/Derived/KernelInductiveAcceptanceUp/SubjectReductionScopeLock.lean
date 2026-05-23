import BEDC.Derived.KernelInductiveAcceptanceUp.ContinuationRouteTotality

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_subject_reduction_scope_lock [AskSetup] [PackageSetup]
    {D S E P R H C Q N sigRead elimRead refuseRead envRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D S sigRead ->
      Cont S E elimRead ->
        Cont P R refuseRead ->
          Cont E R envRead ->
            Cont envRead C scopedRead ->
              PkgSig bundle Q pkg ->
                PkgSig bundle scopedRead pkg ->
                  UnaryHistory D ->
                    UnaryHistory S ->
                      UnaryHistory E ->
                        UnaryHistory P ->
                          UnaryHistory R ->
                            UnaryHistory C ->
                              UnaryHistory elimRead ∧ UnaryHistory envRead ∧
                                UnaryHistory scopedRead ∧ Cont S E elimRead ∧
                                  Cont E R envRead ∧ Cont envRead C scopedRead ∧
                                    List.Mem (kernelInductiveAcceptanceEncodeBHist C)
                                      (kernelInductiveAcceptanceToEventFlow
                                        (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) ∧
                                      PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro declarationSignaturesRead signaturesEliminatorsRead positivityRecursionRead
    eliminatorsRecursionRead envScopedRead packageSig scopedPkg declarationUnary
    signaturesUnary eliminatorsUnary positivityUnary recursionUnary continuationUnary
  have routeFacts :
      UnaryHistory sigRead ∧ UnaryHistory elimRead ∧ UnaryHistory refuseRead ∧
        UnaryHistory envRead ∧ Cont D S sigRead ∧ Cont S E elimRead ∧
          Cont P R refuseRead ∧ Cont E R envRead ∧ PkgSig bundle Q pkg ∧
            List.Mem (kernelInductiveAcceptanceEncodeBHist C)
              (kernelInductiveAcceptanceToEventFlow
                (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) :=
    KernelInductiveAcceptanceUp_cont_route_totality declarationSignaturesRead
      signaturesEliminatorsRead positivityRecursionRead eliminatorsRecursionRead packageSig
      declarationUnary signaturesUnary eliminatorsUnary positivityUnary recursionUnary
      continuationUnary
  obtain ⟨_sigUnary, elimUnary, _refuseUnary, envUnary, _declarationSignaturesRead,
    signaturesEliminatorsReadRow, _positivityRecursionRead, eliminatorsRecursionReadRow,
    _packageSig, continuationListed⟩ := routeFacts
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed envUnary continuationUnary envScopedRead
  exact
    ⟨elimUnary, envUnary, scopedUnary, signaturesEliminatorsReadRow,
      eliminatorsRecursionReadRow, envScopedRead, continuationListed, scopedPkg⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
