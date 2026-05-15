import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnaryContMonoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UnaryContMonoidCarrier [AskSetup] [PackageSetup]
    (a b ab e unitLeft unitRight ledger name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory name ∧ Cont a b ab ∧
    Cont BHist.Empty a unitLeft ∧ Cont a BHist.Empty unitRight ∧
      Cont ab name ledger ∧ PkgSig bundle ledger pkg ∧ hsame e BHist.Empty

theorem UnaryContMonoidCarrier_public_namecert_export [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      UnaryHistory ab /\ UnaryHistory unitLeft /\ UnaryHistory unitRight /\
        UnaryHistory ledger /\ Cont a b ab /\ Cont BHist.Empty a unitLeft /\
          Cont a BHist.Empty unitRight /\ Cont ab name ledger /\ hsame e BHist.Empty /\
            PkgSig bundle ledger pkg /\
              SemanticNameCert
                (fun row : BHist => hsame row ledger /\ UnaryHistory row)
                (fun row : BHist => Cont ab name row /\ hsame e BHist.Empty)
                (fun row : BHist => hsame row ledger /\ PkgSig bundle ledger pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier
  obtain ⟨unaryA, unaryB, unaryName, productRoute, leftUnitRoute, rightUnitRoute,
    ledgerRoute, ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLeftUnit : UnaryHistory unitLeft :=
    unary_cont_closed unary_empty unaryA leftUnitRoute
  have unaryRightUnit : UnaryHistory unitRight :=
    unary_cont_closed unaryA unary_empty rightUnitRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryProduct unaryName ledgerRoute
  have sourceLedger :
      (fun row : BHist => hsame row ledger /\ UnaryHistory row) ledger := by
    exact And.intro (hsame_refl ledger) unaryLedger
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledger /\ UnaryHistory row)
        (fun row : BHist => Cont ab name row /\ hsame e BHist.Empty)
        (fun row : BHist => hsame row ledger /\ PkgSig bundle ledger pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger sourceLedger
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
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact And.intro (cont_result_hsame_transport ledgerRoute (hsame_symm source.left))
          sameUnit
      ledger_sound := by
        intro _row source
        exact And.intro source.left ledgerPkg
    }
  exact
    ⟨unaryProduct, unaryLeftUnit, unaryRightUnit, unaryLedger, productRoute, leftUnitRoute,
      rightUnitRoute, ledgerRoute, sameUnit, ledgerPkg, cert⟩

end BEDC.Derived.UnaryContMonoidUp
