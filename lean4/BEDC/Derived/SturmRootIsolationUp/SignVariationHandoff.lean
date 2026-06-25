import BEDC.Derived.SturmRootIsolationUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SturmRootIsolationCarrier_sign_variation_handoff [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N branchRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B H branchRead →
      Cont branchRead C replayRead →
        PkgSig bundle replayRead pkg →
          UnaryHistory B →
            UnaryHistory H →
              UnaryHistory C →
                UnaryHistory branchRead ∧ UnaryHistory replayRead ∧ Cont B H branchRead ∧
                  Cont branchRead C replayRead ∧ PkgSig bundle replayRead pkg ∧
                    List.Mem (sturmRootIsolationEncodeBHist B)
                      (sturmRootIsolationToEventFlow
                        (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro branchRoute replayRoute replayPkg branchUnary transportUnary replayUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary transportUnary branchRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed branchReadUnary replayUnary replayRoute
  have branchListed :
      List.Mem (sturmRootIsolationEncodeBHist B)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist B)
        [[BMark.b0], sturmRootIsolationEncodeBHist P, [BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist I, [BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist D, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist V,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist W,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          sturmRootIsolationEncodeBHist S,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist Q,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist N]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))))))))
  exact
    ⟨branchReadUnary, replayReadUnary, branchRoute, replayRoute, replayPkg, branchListed⟩

theorem SturmRootIsolationCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N branchRead windowRead handoffRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B W branchRead →
      Cont branchRead R handoffRead →
        Cont handoffRead S sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory B →
              UnaryHistory W →
                UnaryHistory R →
                  UnaryHistory S →
                    UnaryHistory branchRead ∧ UnaryHistory handoffRead ∧
                      UnaryHistory sealRead ∧ Cont handoffRead S sealRead ∧
                        PkgSig bundle sealRead pkg ∧
                          List.Mem (sturmRootIsolationEncodeBHist S)
                            (sturmRootIsolationToEventFlow
                              (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro branchRoute handoffRoute sealRoute sealPkg branchUnary windowUnary handoffUnary
    sealUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary windowUnary branchRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed branchReadUnary handoffUnary handoffRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffReadUnary sealUnary sealRoute
  have sealListed :
      List.Mem (sturmRootIsolationEncodeBHist S)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist S)
        [[BMark.b0], sturmRootIsolationEncodeBHist P, [BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist I, [BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist D, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist V,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist W,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          sturmRootIsolationEncodeBHist S,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist Q,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist N]
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
    left
  exact
    ⟨branchReadUnary, handoffReadUnary, sealReadUnary, sealRoute, sealPkg, sealListed⟩

end BEDC.Derived.SturmRootIsolationUp
