import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyFunctorUp [AskSetup] [PackageSetup]
    (source target modulus readback tolerance transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory source /\
    UnaryHistory target /\
      UnaryHistory modulus /\
        UnaryHistory readback /\
          UnaryHistory tolerance /\
            UnaryHistory transport /\
              UnaryHistory replay /\
                UnaryHistory provenance /\
                  UnaryHistory localName /\
                    Cont source modulus readback /\
                      Cont readback tolerance target /\
                        Cont source target transport /\
                          Cont transport replay provenance /\
                            PkgSig bundle provenance pkg /\
                              PkgSig bundle localName pkg

namespace RegularCauchyFunctorUp

theorem RegularCauchyFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target modulus readback tolerance transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RegularCauchyFunctorUp source target modulus readback tolerance transport
        replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BEDC.Derived.RegularCauchyFunctorUp source target modulus readback tolerance
              transport replay provenance localName bundle pkg /\
            hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.RegularCauchyFunctorUp source target modulus readback tolerance
              transport replay provenance localName bundle pkg /\
            hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.RegularCauchyFunctorUp source target modulus readback tolerance
              transport replay provenance localName bundle pkg /\
            hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro carrier (hsame_refl localName))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end RegularCauchyFunctorUp
end BEDC.Derived
