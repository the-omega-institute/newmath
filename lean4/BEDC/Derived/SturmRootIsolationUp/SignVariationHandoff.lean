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

theorem SturmRootIsolationCarrier_sign_variation_scope [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        PkgSig bundle branchRead pkg →
          UnaryHistory P →
            UnaryHistory V →
              UnaryHistory B →
                UnaryHistory chainRead ∧ UnaryHistory branchRead ∧ Cont P V chainRead ∧
                  Cont chainRead B branchRead ∧ PkgSig bundle branchRead pkg ∧
                    List.Mem (sturmRootIsolationEncodeBHist V)
                      (sturmRootIsolationToEventFlow
                        (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro chainRoute branchRoute branchPkg polynomialUnary variationUnary branchUnary
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed polynomialUnary variationUnary chainRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed chainReadUnary branchUnary branchRoute
  have variationListed :
      List.Mem (sturmRootIsolationEncodeBHist V)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist V)
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
    left
  exact
    ⟨chainReadUnary, branchReadUnary, chainRoute, branchRoute, branchPkg,
      variationListed⟩

theorem SturmRootIsolationCarrier_interval_refinement [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N intervalRead refinedRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I D intervalRead →
      Cont intervalRead W refinedRead →
        Cont refinedRead R windowRead →
          PkgSig bundle windowRead pkg →
            UnaryHistory I →
              UnaryHistory D →
                UnaryHistory W →
                  UnaryHistory R →
                    UnaryHistory intervalRead ∧ UnaryHistory refinedRead ∧
                      UnaryHistory windowRead ∧ Cont I D intervalRead ∧
                        Cont intervalRead W refinedRead ∧ Cont refinedRead R windowRead ∧
                          PkgSig bundle windowRead pkg ∧
                            List.Mem (sturmRootIsolationEncodeBHist D)
                              (sturmRootIsolationToEventFlow
                                (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro intervalRoute refinedRoute windowRoute windowPkg intervalUnary dyadicUnary
    streamUnary readbackUnary
  have intervalReadUnary : UnaryHistory intervalRead :=
    unary_cont_closed intervalUnary dyadicUnary intervalRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed intervalReadUnary streamUnary refinedRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed refinedReadUnary readbackUnary windowRoute
  have dyadicListed :
      List.Mem (sturmRootIsolationEncodeBHist D)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist D)
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
    left
  exact
    ⟨intervalReadUnary, refinedReadUnary, windowReadUnary, intervalRoute, refinedRoute,
      windowRoute, windowPkg, dyadicListed⟩

theorem SturmRootIsolationCarrier_subresultant_sign_variation [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead replayRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        Cont branchRead C replayRead →
          Cont replayRead S sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory P →
                UnaryHistory V →
                  UnaryHistory B →
                    UnaryHistory C →
                      UnaryHistory S →
                        UnaryHistory chainRead ∧ UnaryHistory branchRead ∧
                          UnaryHistory replayRead ∧ UnaryHistory sealRead ∧
                            Cont P V chainRead ∧ Cont chainRead B branchRead ∧
                              Cont branchRead C replayRead ∧ Cont replayRead S sealRead ∧
                                PkgSig bundle sealRead pkg ∧
                                  List.Mem (sturmRootIsolationEncodeBHist V)
                                    (sturmRootIsolationToEventFlow
                                      (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro chainRoute branchRoute replayRoute sealRoute sealPkg polynomialUnary variationUnary
    branchUnary replayUnary sealUnary
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed polynomialUnary variationUnary chainRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed chainReadUnary branchUnary branchRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed branchReadUnary replayUnary replayRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed replayReadUnary sealUnary sealRoute
  have variationListed :
      List.Mem (sturmRootIsolationEncodeBHist V)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist V)
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
    left
  exact
    ⟨chainReadUnary, branchReadUnary, replayReadUnary, sealReadUnary, chainRoute,
      branchRoute, replayRoute, sealRoute, sealPkg, variationListed⟩

end BEDC.Derived.SturmRootIsolationUp
