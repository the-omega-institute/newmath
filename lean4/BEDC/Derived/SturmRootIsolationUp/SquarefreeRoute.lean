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

theorem SturmRootIsolationCarrier_squarefree_route [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead refinedRead windowRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        Cont I D refinedRead →
          Cont refinedRead W windowRead →
            Cont windowRead S sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory P →
                  UnaryHistory V →
                    UnaryHistory B →
                      UnaryHistory I →
                        UnaryHistory D →
                          UnaryHistory W →
                            UnaryHistory S →
                              UnaryHistory chainRead ∧ UnaryHistory branchRead ∧
                                UnaryHistory refinedRead ∧ UnaryHistory windowRead ∧
                                  UnaryHistory sealRead ∧
                                    List.Mem (sturmRootIsolationEncodeBHist P)
                                      (sturmRootIsolationToEventFlow
                                        (SturmRootIsolationUp.mk P I D V B W R S H C Q
                                          N)) ∧
                                      List.Mem (sturmRootIsolationEncodeBHist V)
                                        (sturmRootIsolationToEventFlow
                                          (SturmRootIsolationUp.mk P I D V B W R S H C Q
                                            N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro chainRoute branchRoute refinedRoute windowRoute sealRoute _sealPkg polynomialUnary
    variationUnary branchUnary intervalUnary dyadicUnary windowUnary sealUnary
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed polynomialUnary variationUnary chainRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed chainReadUnary branchUnary branchRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed intervalUnary dyadicUnary refinedRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed refinedReadUnary windowUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary sealRoute
  have polynomialListed :
      List.Mem (sturmRootIsolationEncodeBHist P)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist P)
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
    left
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
    ⟨chainReadUnary, branchReadUnary, refinedReadUnary, windowReadUnary, sealReadUnary,
      polynomialListed, variationListed⟩

end BEDC.Derived.SturmRootIsolationUp
