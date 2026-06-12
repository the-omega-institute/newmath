import BEDC.Derived.RegularCauchyLocatedLimitUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyLocatedLimitRealHandoff [AskSetup] [PackageSetup]
    {W D Q I A R H C P N windowRead readbackRead trapRead locatorRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory I ∧
        UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg) →
      Cont W D windowRead →
        Cont windowRead Q readbackRead →
          Cont readbackRead I trapRead →
            Cont trapRead A locatorRead →
              Cont locatorRead R sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W ∨ hsame row D ∨ hsame row Q ∨ hsame row I ∨
                          hsame row A ∨ hsame row R ∨ hsame row windowRead ∨
                            hsame row readbackRead ∨ hsame row trapRead ∨
                              hsame row locatorRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W D windowRead ∧
                          Cont windowRead Q readbackRead ∧
                            Cont readbackRead I trapRead ∧ Cont trapRead A locatorRead ∧
                              Cont locatorRead R sealRead ∧ PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory trapRead ∧ UnaryHistory locatorRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute readbackRoute trapRoute locatorRoute sealRoute sealPkg
  obtain ⟨wUnary, dUnary, qUnary, iUnary, aUnary, rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _pPkg, _nPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have trapUnary : UnaryHistory trapRead :=
    unary_cont_closed readbackUnary iUnary trapRoute
  have locatorUnary : UnaryHistory locatorRead :=
    unary_cont_closed trapUnary aUnary locatorRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed locatorUnary rUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row Q ∨ hsame row I ∨
              hsame row A ∨ hsame row R ∨ hsame row windowRead ∨
                hsame row readbackRead ∨ hsame row trapRead ∨
                  hsame row locatorRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧ Cont windowRead Q readbackRead ∧
              Cont readbackRead I trapRead ∧ Cont trapRead A locatorRead ∧
                Cont locatorRead R sealRead ∧ PkgSig bundle sealRead pkg)
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
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, readbackRoute, trapRoute, locatorRoute, sealRoute,
          sealPkg⟩
  }
  exact
    ⟨cert, windowUnary, readbackUnary, trapUnary, locatorUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyLocatedLimitUp
