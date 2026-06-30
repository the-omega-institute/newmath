import BEDC.Derived.MaxRateReadGateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MaxRateReadGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MaxRateReadGateNameCertObligations
    {M R S F L H Q C P N rateRead symmetryRead publicRead : BHist} :
    UnaryHistory M →
      UnaryHistory R →
        UnaryHistory S →
          UnaryHistory F →
            UnaryHistory L →
              Cont M R rateRead →
                Cont rateRead S symmetryRead →
                  Cont symmetryRead F publicRead →
                    hsame H Q →
                      hsame P N →
                        SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨
                                  hsame row L ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
                                    hsame row P ∨ hsame row N ∨ hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont M R rateRead ∧
                                  Cont rateRead S symmetryRead ∧
                                    Cont symmetryRead F publicRead ∧ hsame H Q ∧ hsame P N)
                              hsame ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryM unaryR unaryS unaryF _unaryL rateRoute symmetryRoute publicRoute sameHQ
    samePN
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed unaryM unaryR rateRoute
  have symmetryUnary : UnaryHistory symmetryRead :=
    unary_cont_closed rateUnary unaryS symmetryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed symmetryUnary unaryF publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R rateRead ∧ Cont rateRead S symmetryRead ∧
              Cont symmetryRead F publicRead ∧ hsame H Q ∧ hsame P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rateRoute, symmetryRoute, publicRoute, sameHQ, samePN⟩
  }
  exact ⟨cert, publicUnary⟩

theorem MaxRateReadGateCarrier_downstream_consumer_boundary [AskSetup] [PackageSetup]
    {M R S F L H Q C P N symmetryRead refusalRead lockedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory F ∧
      UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory Q ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg →
      Cont R S symmetryRead →
        Cont symmetryRead F refusalRead →
          Cont refusalRead L lockedRead →
            Cont lockedRead C publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨
                        hsame row L ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R S symmetryRead ∧
                        Cont symmetryRead F refusalRead ∧ Cont refusalRead L lockedRead ∧
                          Cont lockedRead C publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory symmetryRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory lockedRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: MaxRateReadGateUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier symmetryRoute refusalRoute lockRoute publicRoute publicPkg
  obtain ⟨_mUnary, rUnary, sUnary, fUnary, lUnary, _hUnary, _qUnary, cUnary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have symmetryUnary : UnaryHistory symmetryRead :=
    unary_cont_closed rUnary sUnary symmetryRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed symmetryUnary fUnary refusalRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed refusalUnary lUnary lockRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lockedUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row S ∨ hsame row F ∨ hsame row L ∨
              hsame row H ∨ hsame row Q ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R S symmetryRead ∧ Cont symmetryRead F refusalRead ∧
              Cont refusalRead L lockedRead ∧ Cont lockedRead C publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, symmetryRoute, refusalRoute, lockRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, symmetryUnary, refusalUnary, lockedUnary, publicUnary⟩

end BEDC.Derived.MaxRateReadGateUp
