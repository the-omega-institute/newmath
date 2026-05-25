import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArchimedeanModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArchimedeanModulusCarrier [AskSetup] [PackageSetup]
    (P D S Q E A H C N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory P ∧ UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory E ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory N ∧ hsame H C ∧ PkgSig bundle N pkg

theorem ArchimedeanModulusNameCertObligations [AskSetup] [PackageSetup]
    {P D S Q E A H C N precisionWindow regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanModulusCarrier P D S Q E A H C N bundle pkg →
      Cont P D precisionWindow →
        Cont precisionWindow Q regularRead →
          Cont regularRead E realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory P ∧ UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                UnaryHistory E ∧ UnaryHistory precisionWindow ∧
                  UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                    Cont P D precisionWindow ∧ Cont precisionWindow Q regularRead ∧
                      Cont regularRead E realRead ∧ hsame H C ∧ PkgSig bundle N pkg ∧
                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier precisionRoute regularRoute realRoute realPkg
  obtain ⟨pUnary, dUnary, sUnary, qUnary, eUnary, _aUnary, _hUnary, _cUnary,
    _nUnary, transportSame, namePkg⟩ := carrier
  have precisionUnary : UnaryHistory precisionWindow :=
    unary_cont_closed pUnary dUnary precisionRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed precisionUnary qUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary eUnary realRoute
  exact
    ⟨pUnary, dUnary, sUnary, qUnary, eUnary, precisionUnary, regularUnary, realUnary,
      precisionRoute, regularRoute, realRoute, transportSame, namePkg, realPkg⟩

end BEDC.Derived.ArchimedeanModulusUp
