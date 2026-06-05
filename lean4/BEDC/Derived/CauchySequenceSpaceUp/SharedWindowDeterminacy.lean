import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceCarrier_shared_window_determinacy [AskSetup] [PackageSetup]
    {F1 sigma1 W1 eps1 Q1 H1 C1 P1 N1 F2 sigma2 W2 eps2 Q2 H2 C2 P2 N2 sharedRead
      leftRoute rightRoute namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier F1 sigma1 W1 eps1 Q1 H1 P1 N1 bundle pkg ->
      CauchySequenceSpaceCarrier F2 sigma2 W2 eps2 Q2 H2 P2 N2 bundle pkg ->
        hsame F1 F2 -> hsame sigma1 sigma2 -> hsame W1 W2 -> hsame eps1 eps2 ->
          hsame Q1 Q2 -> hsame H1 H2 -> hsame C1 C2 -> hsame P1 P2 -> hsame N1 N2 ->
            Cont W1 eps1 sharedRead -> Cont sharedRead Q1 leftRoute ->
              Cont sharedRead Q2 rightRoute -> Cont leftRoute N1 namedRead ->
                PkgSig bundle P1 pkg -> PkgSig bundle N1 pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row F1 ∨ hsame row sigma1 ∨ hsame row W1 ∨
                          hsame row eps1 ∨ hsame row Q1 ∨ hsame row sharedRead ∨
                            hsame row leftRoute ∨ hsame row rightRoute ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W1 eps1 sharedRead ∧
                          Cont sharedRead Q1 leftRoute ∧ Cont sharedRead Q2 rightRoute ∧
                            Cont leftRoute N1 namedRead ∧ PkgSig bundle P1 pkg ∧
                              PkgSig bundle N1 pkg)
                      hsame ∧
                    UnaryHistory sharedRead ∧ UnaryHistory leftRoute ∧
                      UnaryHistory rightRoute ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont PkgSig SemanticNameCert
  intro carrier1 carrier2 _sameFamily _sameSchedule sameWindow sameTolerance sameCompletion
    sameTransport _sameContinuation sameProvenance sameName sharedRoute leftRouteCont rightRouteCont
    namedRoute provenancePkg namePkg
  obtain ⟨_familyUnary1, _scheduleUnary1, windowUnary1, toleranceUnary1, completionUnary1,
    _transportUnary1, _routeUnary1, nameUnary1, windowRoute1, toleranceRoute1,
    completionRoute1, _routePkg1, _namePkg1⟩ := carrier1
  obtain ⟨_familyUnary2, _scheduleUnary2, _windowUnary2, _toleranceUnary2, completionUnary2,
    _transportUnary2, _routeUnary2, _nameUnary2, windowRoute2, toleranceRoute2,
    completionRoute2, _routePkg2, _namePkg2⟩ := carrier2
  have _transportedCompletion : hsame Q1 Q2 :=
    cont_respects_hsame sameWindow sameTolerance toleranceRoute1 toleranceRoute2
  have _transportedRoute : hsame P1 P2 :=
    cont_respects_hsame sameCompletion sameTransport completionRoute1 completionRoute2
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed windowUnary1 toleranceUnary1 sharedRoute
  have leftUnary : UnaryHistory leftRoute :=
    unary_cont_closed sharedUnary completionUnary1 leftRouteCont
  have rightUnary : UnaryHistory rightRoute :=
    unary_cont_closed sharedUnary completionUnary2 rightRouteCont
  have _sameBranch : hsame leftRoute rightRoute :=
    cont_respects_hsame (hsame_refl sharedRead) sameCompletion leftRouteCont rightRouteCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed leftUnary nameUnary1 namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F1 ∨ hsame row sigma1 ∨ hsame row W1 ∨ hsame row eps1 ∨
              hsame row Q1 ∨ hsame row sharedRead ∨ hsame row leftRoute ∨
                hsame row rightRoute ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W1 eps1 sharedRead ∧ Cont sharedRead Q1 leftRoute ∧
              Cont sharedRead Q2 rightRoute ∧ Cont leftRoute N1 namedRead ∧
                PkgSig bundle P1 pkg ∧ PkgSig bundle N1 pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sharedRoute, leftRouteCont, rightRouteCont, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, sharedUnary, leftUnary, rightUnary, namedUnary⟩

end BEDC.Derived.CauchySequenceSpaceUp
