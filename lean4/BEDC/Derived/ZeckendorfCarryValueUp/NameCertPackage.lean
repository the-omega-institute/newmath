import BEDC.Derived.AxisZeckendorf.Carry
import BEDC.Derived.ZeckendorfCarryValueUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ZeckendorfCarryValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Derived.AxisZeckendorf.Carry

theorem ZeckendorfCarryValueCarrier_namecert_package [AskSetup] [PackageSetup]
    {h k G sourceNormal targetNormal valueRow boundary route provenance localName valueRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZCarry h k ->
      Cont G valueRow valueRead ->
        Cont valueRead route publicRead ->
          PkgSig bundle publicRead pkg ->
            (¬ hsame h k) /\ Cont G valueRow valueRead /\
              Cont valueRead route publicRead /\ PkgSig bundle publicRead pkg /\
                SemanticNameCert
                  (fun row : BHist => hsame row publicRead)
                  (fun row : BHist =>
                    hsame row h \/ hsame row k \/ hsame row valueRow \/
                      hsame row boundary \/ hsame row publicRead)
                  (fun row : BHist => PkgSig bundle publicRead pkg /\ hsame row publicRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert ZCarry
  intro carry valueRoute publicRoute publicPkg
  have notSame : ¬ hsame h k := zCarry_not_hsame carry
  have sourcePublic : (fun row : BHist => hsame row publicRead) publicRead :=
    hsame_refl publicRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead)
        (fun row : BHist =>
          hsame row h \/ hsame row k \/ hsame row valueRow \/ hsame row boundary \/
            hsame row publicRead)
        (fun row : BHist => PkgSig bundle publicRead pkg /\ hsame row publicRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead sourcePublic
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source)))
      ledger_sound := by
        intro _row source
        exact ⟨publicPkg, source⟩
    }
  exact ⟨notSame, valueRoute, publicRoute, publicPkg, cert⟩

end BEDC.Derived.ZeckendorfCarryValueUp
