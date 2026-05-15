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

theorem UnaryContMonoidCarrier_unit_bind_surface [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name unitBindRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont unitLeft unitRight unitBindRead ->
        PkgSig bundle unitBindRead pkg ->
          UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory ab ∧ UnaryHistory unitLeft ∧
            UnaryHistory unitRight ∧ UnaryHistory unitBindRead ∧ Cont a b ab ∧
              Cont BHist.Empty a unitLeft ∧ Cont a BHist.Empty unitRight ∧
                Cont unitLeft unitRight unitBindRead ∧ hsame e BHist.Empty ∧
                  PkgSig bundle unitBindRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row unitBindRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        Cont unitLeft unitRight row ∧ hsame e BHist.Empty)
                      (fun row : BHist =>
                        hsame row unitBindRead ∧ PkgSig bundle unitBindRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unitBindRoute unitBindPkg
  obtain ⟨unaryA, unaryB, _unaryName, productRoute, leftUnitRoute, rightUnitRoute,
    _ledgerRoute, _ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLeftUnit : UnaryHistory unitLeft :=
    unary_cont_closed unary_empty unaryA leftUnitRoute
  have unaryRightUnit : UnaryHistory unitRight :=
    unary_cont_closed unaryA unary_empty rightUnitRoute
  have unaryUnitBindRead : UnaryHistory unitBindRead :=
    unary_cont_closed unaryLeftUnit unaryRightUnit unitBindRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row unitBindRead ∧ UnaryHistory row)
        (fun row : BHist => Cont unitLeft unitRight row ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row unitBindRead ∧ PkgSig bundle unitBindRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro unitBindRead
            (And.intro (hsame_refl unitBindRead) unaryUnitBindRead)
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨cont_result_hsame_transport unitBindRoute (hsame_symm source.left), sameUnit⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left unitBindPkg
    }
  exact
    ⟨unaryA, unaryB, unaryProduct, unaryLeftUnit, unaryRightUnit, unaryUnitBindRead,
      productRoute, leftUnitRoute, rightUnitRoute, unitBindRoute, sameUnit, unitBindPkg, cert⟩

theorem UnaryContMonoidCarrier_operation_closure [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      UnaryHistory ab ∧ Cont a b ab ∧ Cont BHist.Empty a unitLeft ∧
        Cont a BHist.Empty unitRight ∧ UnaryHistory unitLeft ∧
          UnaryHistory unitRight ∧ hsame e BHist.Empty := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier
  obtain ⟨unaryA, unaryB, _unaryName, productRoute, leftUnitRoute, rightUnitRoute,
    _ledgerRoute, _ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLeftUnit : UnaryHistory unitLeft :=
    unary_cont_closed unary_empty unaryA leftUnitRoute
  have unaryRightUnit : UnaryHistory unitRight :=
    unary_cont_closed unaryA unary_empty rightUnitRoute
  exact
    ⟨unaryProduct, productRoute, leftUnitRoute, rightUnitRoute, unaryLeftUnit,
      unaryRightUnit, sameUnit⟩

theorem UnaryContMonoidCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont ledger name obligationRead ->
        PkgSig bundle obligationRead pkg ->
          UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory ab ∧ UnaryHistory unitLeft ∧
            UnaryHistory unitRight ∧ UnaryHistory ledger ∧ UnaryHistory name ∧
              UnaryHistory obligationRead ∧ Cont a b ab ∧
                Cont BHist.Empty a unitLeft ∧ Cont a BHist.Empty unitRight ∧
                  Cont ab name ledger ∧ Cont ledger name obligationRead ∧
                    hsame e BHist.Empty ∧ PkgSig bundle ledger pkg ∧
                      PkgSig bundle obligationRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            Cont ledger name row ∧ hsame e BHist.Empty)
                          (fun row : BHist =>
                            hsame row obligationRead ∧ PkgSig bundle obligationRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier obligationRoute obligationPkg
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
  have unaryObligation : UnaryHistory obligationRead :=
    unary_cont_closed unaryLedger unaryName obligationRoute
  have sourceObligation :
      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row) obligationRead := by
    exact ⟨hsame_refl obligationRead, unaryObligation⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
        (fun row : BHist => Cont ledger name row ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row obligationRead ∧ PkgSig bundle obligationRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro obligationRead sourceObligation
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨cont_result_hsame_transport obligationRoute (hsame_symm source.left),
            sameUnit⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, obligationPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryProduct, unaryLeftUnit, unaryRightUnit, unaryLedger,
      unaryName, unaryObligation, productRoute, leftUnitRoute, rightUnitRoute,
      ledgerRoute, obligationRoute, sameUnit, ledgerPkg, obligationPkg, cert⟩

theorem UnaryContMonoidCarrier_cont_associativity [AskSetup] [PackageSetup]
    {a b c ab bc abc abc' e unitLeft unitRight ledger name assocRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      UnaryHistory c ->
        Cont b c bc ->
          Cont ab c abc ->
            Cont a bc abc' ->
              Cont abc name assocRead ->
                PkgSig bundle assocRead pkg ->
                  hsame abc abc' ∧ UnaryHistory bc ∧ UnaryHistory abc ∧
                    UnaryHistory abc' ∧ UnaryHistory assocRead ∧
                      PkgSig bundle assocRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row assocRead ∧ UnaryHistory row)
                          (fun row : BHist => Cont abc name row ∧ hsame abc abc')
                          (fun row : BHist =>
                            hsame row assocRead ∧ PkgSig bundle assocRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier unaryC routeBC routeABC routeABC' routeAssoc assocPkg
  obtain ⟨unaryA, unaryB, unaryName, productRoute, _leftUnitRoute, _rightUnitRoute,
    _ledgerRoute, _ledgerPkg, _sameUnit⟩ := carrier
  have assocSame : hsame abc abc' :=
    cont_assoc_hsame productRoute routeABC routeBC routeABC'
  have unaryBC : UnaryHistory bc :=
    unary_cont_closed unaryB unaryC routeBC
  have unaryABC : UnaryHistory abc :=
    unary_cont_closed (unary_cont_closed unaryA unaryB productRoute) unaryC routeABC
  have unaryABC' : UnaryHistory abc' :=
    unary_cont_closed unaryA unaryBC routeABC'
  have unaryAssocRead : UnaryHistory assocRead :=
    unary_cont_closed unaryABC unaryName routeAssoc
  have sourceAssoc :
      (fun row : BHist => hsame row assocRead ∧ UnaryHistory row) assocRead := by
    exact ⟨hsame_refl assocRead, unaryAssocRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row assocRead ∧ UnaryHistory row)
        (fun row : BHist => Cont abc name row ∧ hsame abc abc')
        (fun row : BHist => hsame row assocRead ∧ PkgSig bundle assocRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro assocRead sourceAssoc
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨cont_result_hsame_transport routeAssoc (hsame_symm source.left),
            assocSame⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, assocPkg⟩
    }
  exact
    ⟨assocSame, unaryBC, unaryABC, unaryABC', unaryAssocRead, assocPkg, cert⟩

end BEDC.Derived.UnaryContMonoidUp
