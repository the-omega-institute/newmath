import BEDC.Derived.SturmRootIsolationUp.SignVariationHandoff
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SturmRootIsolationCarrier_scoped_kernel_binding [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        Cont branchRead S sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory P →
              UnaryHistory V →
                UnaryHistory B →
                  UnaryHistory S →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨
                            hsame row B ∨ hsame row W ∨ hsame row R ∨ hsame row S ∨
                              hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N ∨
                                hsame row sealRead)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                        hsame ∧
                      UnaryHistory chainRead ∧ UnaryHistory branchRead ∧
                        UnaryHistory sealRead ∧
                          List.Mem (sturmRootIsolationEncodeBHist V)
                            (sturmRootIsolationToEventFlow
                              (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) ∧
                            List.Mem (sturmRootIsolationEncodeBHist S)
                              (sturmRootIsolationToEventFlow
                                (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro chainRoute branchRoute sealRoute sealPkg polynomialUnary variationUnary branchUnary
    sealUnary
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed polynomialUnary variationUnary chainRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed chainReadUnary branchUnary branchRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed branchReadUnary sealUnary sealRoute
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨
              hsame row B ∨ hsame row W ∨ hsame row R ∨ hsame row S ∨
                hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N ∨
                  hsame row sealRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg⟩
  }
  exact
    ⟨cert, chainReadUnary, branchReadUnary, sealReadUnary, variationListed, sealListed⟩

theorem SturmRootIsolationCarrier_scoped_interval_real_seal_route [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead intervalRead refinedRead readbackRead
      sealRead realRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        Cont I D intervalRead →
          Cont intervalRead W refinedRead →
            Cont refinedRead R readbackRead →
              Cont branchRead S sealRead →
                Cont readbackRead sealRead realRoute →
                  PkgSig bundle realRoute pkg →
                    UnaryHistory P →
                      UnaryHistory V →
                        UnaryHistory B →
                          UnaryHistory I →
                            UnaryHistory D →
                              UnaryHistory W →
                                UnaryHistory R →
                                  UnaryHistory S →
                                    SemanticNameCert
                                        (fun row : BHist => hsame row realRoute ∧
                                          UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row P ∨ hsame row I ∨ hsame row D ∨
                                            hsame row V ∨ hsame row B ∨ hsame row W ∨
                                              hsame row R ∨ hsame row S ∨
                                                hsame row chainRead ∨ hsame row branchRead ∨
                                                  hsame row intervalRead ∨
                                                    hsame row refinedRead ∨
                                                      hsame row readbackRead ∨
                                                        hsame row sealRead ∨
                                                          hsame row realRoute)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont P V chainRead ∧
                                            Cont chainRead B branchRead ∧
                                              Cont I D intervalRead ∧
                                                Cont intervalRead W refinedRead ∧
                                                  Cont refinedRead R readbackRead ∧
                                                    Cont branchRead S sealRead ∧
                                                      Cont readbackRead sealRead realRoute ∧
                                                        PkgSig bundle realRoute pkg)
                                        hsame ∧
                                      UnaryHistory chainRead ∧ UnaryHistory branchRead ∧
                                        UnaryHistory intervalRead ∧ UnaryHistory refinedRead ∧
                                          UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                                            UnaryHistory realRoute ∧
                                              List.Mem (sturmRootIsolationEncodeBHist V)
                                                (sturmRootIsolationToEventFlow
                                                  (SturmRootIsolationUp.mk P I D V B W R S H C
                                                    Q N)) ∧
                                                List.Mem (sturmRootIsolationEncodeBHist D)
                                                  (sturmRootIsolationToEventFlow
                                                    (SturmRootIsolationUp.mk P I D V B W R S H C
                                                      Q N)) ∧
                                                  List.Mem (sturmRootIsolationEncodeBHist S)
                                                    (sturmRootIsolationToEventFlow
                                                      (SturmRootIsolationUp.mk P I D V B W R S H
                                                        C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro chainRoute branchRoute intervalRoute refinedRoute readbackRoute sealRoute realRouteCont
    realPkg polynomialUnary variationUnary branchUnary intervalUnary dyadicUnary windowUnary
    readbackUnary sealUnary
  have chainReadUnary : UnaryHistory chainRead :=
    unary_cont_closed polynomialUnary variationUnary chainRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed chainReadUnary branchUnary branchRoute
  have intervalReadUnary : UnaryHistory intervalRead :=
    unary_cont_closed intervalUnary dyadicUnary intervalRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed intervalReadUnary windowUnary refinedRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed refinedReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed branchReadUnary sealUnary sealRoute
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed readbackReadUnary sealReadUnary realRouteCont
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
    right; right; right; right; right; right; right; left
  have dyadicListed :
      List.Mem (sturmRootIsolationEncodeBHist D)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist D)
        [[BMark.b0], sturmRootIsolationEncodeBHist P, [BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist I, [BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist D,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0], sturmRootIsolationEncodeBHist V,
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
    right; right; right; right; right; left
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
    right; right; right; right; right; right; right; right
    right; right; right; right; right; right; right; left
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨ hsame row B ∨
              hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row chainRead ∨
                hsame row branchRead ∨ hsame row intervalRead ∨ hsame row refinedRead ∨
                  hsame row readbackRead ∨ hsame row sealRead ∨ hsame row realRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P V chainRead ∧ Cont chainRead B branchRead ∧
              Cont I D intervalRead ∧ Cont intervalRead W refinedRead ∧
                Cont refinedRead R readbackRead ∧ Cont branchRead S sealRead ∧
                  Cont readbackRead sealRead realRoute ∧ PkgSig bundle realRoute pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRoute ⟨hsame_refl realRoute, realRouteUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, chainRoute, branchRoute, intervalRoute, refinedRoute, readbackRoute,
          sealRoute, realRouteCont, realPkg⟩
  }
  exact
    ⟨cert, chainReadUnary, branchReadUnary, intervalReadUnary, refinedReadUnary,
      readbackReadUnary, sealReadUnary, realRouteUnary, variationListed, dyadicListed,
      sealListed⟩

theorem SturmRootIsolationCarrier_sign_variation_scope_real_seal_consumer [AskSetup]
    [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead intervalRead refinedRead readbackRead
      sealRead realRoute : BHist}
    {bundle : ProbeBundle ProbeName} {branchPkg routePkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        Cont I D intervalRead →
          Cont intervalRead W refinedRead →
            Cont refinedRead R readbackRead →
              Cont branchRead S sealRead →
                Cont readbackRead sealRead realRoute →
                  PkgSig bundle branchRead branchPkg →
                    PkgSig bundle realRoute routePkg →
                      UnaryHistory P →
                        UnaryHistory V →
                          UnaryHistory B →
                            UnaryHistory I →
                              UnaryHistory D →
                                UnaryHistory W →
                                  UnaryHistory R →
                                    UnaryHistory S →
                                      SemanticNameCert
                                          (fun row : BHist => hsame row realRoute ∧
                                            UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row P ∨ hsame row I ∨ hsame row D ∨
                                              hsame row V ∨ hsame row B ∨ hsame row W ∨
                                                hsame row R ∨ hsame row S ∨
                                                  hsame row chainRead ∨
                                                    hsame row branchRead ∨
                                                      hsame row intervalRead ∨
                                                        hsame row refinedRead ∨
                                                          hsame row readbackRead ∨
                                                            hsame row sealRead ∨
                                                              hsame row realRoute)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont P V chainRead ∧
                                              Cont chainRead B branchRead ∧
                                                Cont I D intervalRead ∧
                                                  Cont intervalRead W refinedRead ∧
                                                    Cont refinedRead R readbackRead ∧
                                                      Cont branchRead S sealRead ∧
                                                        Cont readbackRead sealRead realRoute ∧
                                                          PkgSig bundle realRoute routePkg)
                                          hsame ∧
                                        UnaryHistory chainRead ∧ UnaryHistory branchRead ∧
                                          UnaryHistory realRoute ∧ Cont P V chainRead ∧
                                            Cont chainRead B branchRead ∧
                                              PkgSig bundle branchRead branchPkg ∧
                                                List.Mem (sturmRootIsolationEncodeBHist V)
                                                  (sturmRootIsolationToEventFlow
                                                    (SturmRootIsolationUp.mk P I D V B W R S H C
                                                      Q N)) ∧
                                                  List.Mem (sturmRootIsolationEncodeBHist S)
                                                    (sturmRootIsolationToEventFlow
                                                      (SturmRootIsolationUp.mk P I D V B W R S H
                                                        C Q N)) := by
  intro chainRoute branchRoute intervalRoute refinedRoute readbackRoute sealRoute realRouteCont
    branchPkgSig routePkgSig polynomialUnary variationUnary branchUnary intervalUnary dyadicUnary
    windowUnary readbackUnary sealUnary
  have scope :=
    SturmRootIsolationCarrier_sign_variation_scope
      (P := P) (I := I) (D := D) (V := V) (B := B) (W := W) (R := R) (S := S)
      (H := H) (C := C) (Q := Q) (N := N) (chainRead := chainRead)
      (branchRead := branchRead) (bundle := bundle) (pkg := branchPkg)
      chainRoute branchRoute branchPkgSig polynomialUnary variationUnary branchUnary
  have route :=
    SturmRootIsolationCarrier_scoped_interval_real_seal_route
      (P := P) (I := I) (D := D) (V := V) (B := B) (W := W) (R := R) (S := S)
      (H := H) (C := C) (Q := Q) (N := N) (chainRead := chainRead)
      (branchRead := branchRead) (intervalRead := intervalRead) (refinedRead := refinedRead)
      (readbackRead := readbackRead) (sealRead := sealRead) (realRoute := realRoute)
      (bundle := bundle) (pkg := routePkg)
      chainRoute branchRoute intervalRoute refinedRoute readbackRoute sealRoute realRouteCont
      routePkgSig polynomialUnary variationUnary branchUnary intervalUnary dyadicUnary windowUnary
      readbackUnary sealUnary
  have chainReadUnary : UnaryHistory chainRead := scope.left
  have branchReadUnary : UnaryHistory branchRead := scope.right.left
  have realRouteUnary : UnaryHistory realRoute :=
    route.right.right.right.right.right.right.right.left
  have chainRouteOut : Cont P V chainRead := scope.right.right.left
  have branchRouteOut : Cont chainRead B branchRead := scope.right.right.right.left
  have branchPkgOut : PkgSig bundle branchRead branchPkg :=
    scope.right.right.right.right.left
  have variationListed :
      List.Mem (sturmRootIsolationEncodeBHist V)
        (sturmRootIsolationToEventFlow (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) :=
    scope.right.right.right.right.right
  have sealListed :
      List.Mem (sturmRootIsolationEncodeBHist S)
        (sturmRootIsolationToEventFlow (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) :=
    route.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨route.left, chainReadUnary, branchReadUnary, realRouteUnary, chainRouteOut, branchRouteOut,
      branchPkgOut, variationListed, sealListed⟩

theorem SturmRootIsolationCarrier_interval_refinement_real_seal_consumer [AskSetup]
    [PackageSetup]
    {P I D V B W R S H C Q N chainRead branchRead intervalRead refinedRead readbackRead
      sealRead realRoute : BHist}
    {bundle : ProbeBundle ProbeName} {windowPkg routePkg : Pkg} :
    Cont P V chainRead →
      Cont chainRead B branchRead →
        Cont I D intervalRead →
          Cont intervalRead W refinedRead →
            Cont refinedRead R readbackRead →
              Cont branchRead S sealRead →
                Cont readbackRead sealRead realRoute →
                  PkgSig bundle readbackRead windowPkg →
                    PkgSig bundle realRoute routePkg →
                      UnaryHistory P →
                        UnaryHistory V →
                          UnaryHistory B →
                            UnaryHistory I →
                              UnaryHistory D →
                                UnaryHistory W →
                                  UnaryHistory R →
                                    UnaryHistory S →
                                      SemanticNameCert
                                          (fun row : BHist => hsame row realRoute ∧
                                            UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row P ∨ hsame row I ∨ hsame row D ∨
                                              hsame row V ∨ hsame row B ∨ hsame row W ∨
                                                hsame row R ∨ hsame row S ∨
                                                  hsame row chainRead ∨
                                                    hsame row branchRead ∨
                                                      hsame row intervalRead ∨
                                                        hsame row refinedRead ∨
                                                          hsame row readbackRead ∨
                                                            hsame row sealRead ∨
                                                              hsame row realRoute)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont P V chainRead ∧
                                              Cont chainRead B branchRead ∧
                                                Cont I D intervalRead ∧
                                                  Cont intervalRead W refinedRead ∧
                                                    Cont refinedRead R readbackRead ∧
                                                      Cont branchRead S sealRead ∧
                                                        Cont readbackRead sealRead realRoute ∧
                                                          PkgSig bundle realRoute routePkg)
                                          hsame ∧
                                        UnaryHistory intervalRead ∧ UnaryHistory refinedRead ∧
                                          UnaryHistory readbackRead ∧ UnaryHistory realRoute ∧
                                            Cont I D intervalRead ∧
                                              Cont intervalRead W refinedRead ∧
                                                Cont refinedRead R readbackRead ∧
                                                  PkgSig bundle readbackRead windowPkg ∧
                                                    List.Mem (sturmRootIsolationEncodeBHist D)
                                                      (sturmRootIsolationToEventFlow
                                                        (SturmRootIsolationUp.mk P I D V B W R
                                                          S H C Q N)) ∧
                                                      List.Mem (sturmRootIsolationEncodeBHist S)
                                                        (sturmRootIsolationToEventFlow
                                                          (SturmRootIsolationUp.mk P I D V B W
                                                            R S H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro chainRoute branchRoute intervalRoute refinedRoute readbackRoute sealRoute realRouteCont
    windowPkgSig routePkgSig polynomialUnary variationUnary branchUnary intervalUnary dyadicUnary
    windowUnary readbackUnary sealUnary
  have refinement :=
    SturmRootIsolationCarrier_interval_refinement
      (P := P) (I := I) (D := D) (V := V) (B := B) (W := W) (R := R) (S := S)
      (H := H) (C := C) (Q := Q) (N := N) (intervalRead := intervalRead)
      (refinedRead := refinedRead) (windowRead := readbackRead) (bundle := bundle)
      (pkg := windowPkg)
      intervalRoute refinedRoute readbackRoute windowPkgSig intervalUnary dyadicUnary
      windowUnary readbackUnary
  have route :=
    SturmRootIsolationCarrier_scoped_interval_real_seal_route
      (P := P) (I := I) (D := D) (V := V) (B := B) (W := W) (R := R) (S := S)
      (H := H) (C := C) (Q := Q) (N := N) (chainRead := chainRead)
      (branchRead := branchRead) (intervalRead := intervalRead) (refinedRead := refinedRead)
      (readbackRead := readbackRead) (sealRead := sealRead) (realRoute := realRoute)
      (bundle := bundle) (pkg := routePkg)
      chainRoute branchRoute intervalRoute refinedRoute readbackRoute sealRoute realRouteCont
      routePkgSig polynomialUnary variationUnary branchUnary intervalUnary dyadicUnary windowUnary
      readbackUnary sealUnary
  have intervalReadUnary : UnaryHistory intervalRead := refinement.left
  have refinedReadUnary : UnaryHistory refinedRead := refinement.right.left
  have readbackReadUnary : UnaryHistory readbackRead := refinement.right.right.left
  have realRouteUnary : UnaryHistory realRoute :=
    route.right.right.right.right.right.right.right.left
  have intervalRouteOut : Cont I D intervalRead := refinement.right.right.right.left
  have refinedRouteOut : Cont intervalRead W refinedRead :=
    refinement.right.right.right.right.left
  have readbackRouteOut : Cont refinedRead R readbackRead :=
    refinement.right.right.right.right.right.left
  have windowPkgOut : PkgSig bundle readbackRead windowPkg :=
    refinement.right.right.right.right.right.right.left
  have dyadicListed :
      List.Mem (sturmRootIsolationEncodeBHist D)
        (sturmRootIsolationToEventFlow (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) :=
    refinement.right.right.right.right.right.right.right
  have sealListed :
      List.Mem (sturmRootIsolationEncodeBHist S)
        (sturmRootIsolationToEventFlow (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) :=
    route.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨route.left, intervalReadUnary, refinedReadUnary, readbackReadUnary, realRouteUnary,
      intervalRouteOut, refinedRouteOut, readbackRouteOut, windowPkgOut, dyadicListed,
      sealListed⟩

end BEDC.Derived.SturmRootIsolationUp
