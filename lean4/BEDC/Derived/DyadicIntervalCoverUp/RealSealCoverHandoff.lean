import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRealSealCoverHandoff [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead coverRead membershipRead coverWindowRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) →
      Cont W Q windowRead →
        Cont M R coverRead →
          Cont V coverRead membershipRead →
            Cont windowRead membershipRead coverWindowRead →
              Cont coverWindowRead A sealRead →
                PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
                        hsame row V ∨ hsame row windowRead ∨ hsame row coverRead ∨
                          hsame row membershipRead ∨ hsame row coverWindowRead ∨
                            hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
                        Cont V coverRead membershipRead ∧
                          Cont windowRead membershipRead coverWindowRead ∧
                            Cont coverWindowRead A sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧ UnaryHistory windowRead ∧ UnaryHistory coverRead ∧
                  UnaryHistory membershipRead ∧ UnaryHistory coverWindowRead ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrierRows windowRoute coverRoute membershipRoute coverWindowRoute sealRoute
    sealPkg
  obtain ⟨_unaryL, _unaryU, mUnary, rUnary, vUnary, wUnary, qUnary, aUnary,
    _unaryH, _unaryC, _unaryP, _unaryN, _provenancePkg⟩ := carrierRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed vUnary coverUnary membershipRoute
  have coverWindowUnary : UnaryHistory coverWindowRead :=
    unary_cont_closed windowUnary membershipUnary coverWindowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverWindowUnary aUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row windowRead ∨ hsame row coverRead ∨
                hsame row membershipRead ∨ hsame row coverWindowRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W Q windowRead ∧ Cont M R coverRead ∧
              Cont V coverRead membershipRead ∧
                Cont windowRead membershipRead coverWindowRead ∧
                  Cont coverWindowRead A sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, coverRoute, membershipRoute, coverWindowRoute,
          sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, coverUnary, membershipUnary, coverWindowUnary, sealUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
