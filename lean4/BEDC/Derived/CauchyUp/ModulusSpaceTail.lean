import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusSpaceTailComposition [AskSetup] [PackageSetup]
    {I S W D R Q H C P N scheduleRead windowRead toleranceRead readbackRead sealRead
      structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N →
      Cont I S scheduleRead →
        Cont scheduleRead W windowRead →
          Cont windowRead D toleranceRead →
            Cont toleranceRead R readbackRead →
              Cont readbackRead Q sealRead →
                Cont H C structuralRead →
                  Cont P N namedRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row I ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
                                hsame row R ∨ hsame row Q ∨ hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory scheduleRead ∧ UnaryHistory windowRead ∧
                            UnaryHistory toleranceRead ∧ UnaryHistory readbackRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory structuralRead ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier scheduleRoute windowRoute toleranceRoute readbackRoute sealRoute
    structuralRoute namingRoute provenancePkg namePkg
  obtain ⟨iUnary, sUnary, wUnary, dUnary, rUnary, qUnary, hUnary, cUnary, pUnary,
    nUnary⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed iUnary sUnary scheduleRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed scheduleReadUnary wUnary windowRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowReadUnary dUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary rUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary qUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namingRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  · exact
      ⟨scheduleReadUnary, windowReadUnary, toleranceReadUnary, readbackReadUnary,
        sealReadUnary, structuralReadUnary, namedReadUnary⟩

theorem CauchyCompletionLeftExactnessRegSeqRatUnitPullback [AskSetup] [PackageSetup]
    {S U D K E H C P N regRead realSeal extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionLeftExactnessCarrier S U D K E H C P N ->
      Cont K E regRead ->
        Cont regRead N realSeal ->
          Cont realSeal H extensionRead ->
            PkgSig bundle extensionRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row K ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row regRead ∨ hsame row realSeal ∨
                          hsame row extensionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle extensionRead pkg ∧
                      Cont K E regRead)
                  hsame ∧
                UnaryHistory regRead ∧ UnaryHistory realSeal ∧
                  UnaryHistory extensionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier regRoute realSealRoute extensionRoute extensionPkg
  obtain ⟨_sUnary, _uUnary, _dUnary, kUnary, eUnary, hUnary, _cUnary, _pUnary,
    nUnary⟩ := carrier
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed kUnary eUnary regRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary nUnary realSealRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed realSealUnary hUnary extensionRoute
  have sourceExtension :
      (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row) extensionRead := by
    exact ⟨hsame_refl extensionRead, extensionReadUnary⟩
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro extensionRead sourceExtension
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
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, extensionPkg, regRoute⟩
    }
  · exact ⟨regReadUnary, realSealUnary, extensionReadUnary⟩

end BEDC.Derived.CauchyUp
