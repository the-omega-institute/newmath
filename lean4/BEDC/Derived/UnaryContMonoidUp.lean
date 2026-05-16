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

theorem UnaryContMonoidCarrier_scoped_grounding [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont unitLeft ledger scopedRead ->
        PkgSig bundle scopedRead pkg ->
          UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory ab ∧ UnaryHistory unitLeft ∧
            UnaryHistory ledger ∧ UnaryHistory scopedRead ∧ Cont a b ab ∧
              Cont BHist.Empty a unitLeft ∧ Cont ab name ledger ∧
                Cont unitLeft ledger scopedRead ∧ hsame e BHist.Empty ∧
                  PkgSig bundle scopedRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        Cont unitLeft ledger row ∧ hsame e BHist.Empty)
                      (fun row : BHist =>
                        hsame row scopedRead ∧ PkgSig bundle scopedRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier scopedRoute scopedPkg
  obtain ⟨unaryA, unaryB, unaryName, productRoute, leftUnitRoute, _rightUnitRoute,
    ledgerRoute, _ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLeftUnit : UnaryHistory unitLeft :=
    unary_cont_closed unary_empty unaryA leftUnitRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryProduct unaryName ledgerRoute
  have unaryScoped : UnaryHistory scopedRead :=
    unary_cont_closed unaryLeftUnit unaryLedger scopedRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, unaryScoped⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
        (fun row : BHist => Cont unitLeft ledger row ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row scopedRead ∧ PkgSig bundle scopedRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopedRead sourceScoped
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
          ⟨cont_result_hsame_transport scopedRoute (hsame_symm source.left),
            sameUnit⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, scopedPkg⟩
    }
  exact
    ⟨unaryA, unaryB, unaryProduct, unaryLeftUnit, unaryLedger, unaryScoped,
      productRoute, leftUnitRoute, ledgerRoute, scopedRoute, sameUnit, scopedPkg, cert⟩

theorem UnaryContMonoidCarrier_sibling_dependency [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name siblingK siblingL : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont b name siblingK ->
        Cont siblingK e siblingL ->
          PkgSig bundle siblingL pkg ->
            UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory ab ∧ UnaryHistory siblingK ∧
              UnaryHistory siblingL ∧ Cont a b ab ∧ Cont b name siblingK ∧
                Cont siblingK e siblingL ∧ hsame e BHist.Empty ∧
                  PkgSig bundle ledger pkg ∧ PkgSig bundle siblingL pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier siblingRoute tailRoute siblingPkg
  obtain ⟨unaryA, unaryB, unaryName, productRoute, _leftUnitRoute, _rightUnitRoute,
    _ledgerRoute, ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have siblingKUnary : UnaryHistory siblingK :=
    unary_cont_closed unaryB unaryName siblingRoute
  have unitUnary : UnaryHistory e :=
    unary_transport unary_empty (hsame_symm sameUnit)
  have siblingLUnary : UnaryHistory siblingL :=
    unary_cont_closed siblingKUnary unitUnary tailRoute
  exact
    ⟨unaryA, unaryB, unaryProduct, siblingKUnary, siblingLUnary, productRoute,
      siblingRoute, tailRoute, sameUnit, ledgerPkg, siblingPkg⟩

theorem UnaryContMonoidCarrier_public_formal_target [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont ledger name formalRead ->
        PkgSig bundle formalRead pkg ->
          UnaryHistory formalRead ∧ Cont ledger name formalRead ∧
            PkgSig bundle formalRead pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row formalRead ∧ Cont ledger name formalRead ∧
                    hsame e BHist.Empty)
                (fun row : BHist => hsame row formalRead ∧ PkgSig bundle formalRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier formalRoute formalPkg
  obtain ⟨unaryA, unaryB, unaryName, productRoute, _leftUnitRoute, _rightUnitRoute,
    ledgerRoute, _ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryProduct unaryName ledgerRoute
  have unaryFormalRead : UnaryHistory formalRead :=
    unary_cont_closed unaryLedger unaryName formalRoute
  have sourceFormal :
      (fun row : BHist => hsame row formalRead ∧ UnaryHistory row) formalRead := by
    exact ⟨hsame_refl formalRead, unaryFormalRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row formalRead ∧ Cont ledger name formalRead ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row formalRead ∧ PkgSig bundle formalRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro formalRead sourceFormal
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
        exact ⟨source.left, formalRoute, sameUnit⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, formalPkg⟩
    }
  exact ⟨unaryFormalRead, formalRoute, formalPkg, cert⟩

def UnaryContMonoidKernelScope [AskSetup] [PackageSetup]
    (a b ab e unitLeft unitRight ledger name scopeRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ∧
    Cont unitLeft ledger scopeRead ∧ PkgSig bundle scopeRead pkg ∧
      SemanticNameCert
        (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
        (fun row : BHist => Cont unitLeft ledger row ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
        hsame

theorem UnaryContMonoidKernelScope_namecert_surface [AskSetup] [PackageSetup]
    {a b ab e unitLeft unitRight ledger name scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg ->
      Cont unitLeft ledger scopeRead ->
        PkgSig bundle scopeRead pkg ->
          UnaryContMonoidKernelScope a b ab e unitLeft unitRight ledger name scopeRead
            bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier scopeRoute scopePkg
  have carrierWitness :
      UnaryContMonoidCarrier a b ab e unitLeft unitRight ledger name bundle pkg := carrier
  obtain ⟨unaryA, unaryB, unaryName, productRoute, leftUnitRoute, _rightUnitRoute,
    ledgerRoute, _ledgerPkg, sameUnit⟩ := carrier
  have unaryProduct : UnaryHistory ab :=
    unary_cont_closed unaryA unaryB productRoute
  have unaryLeftUnit : UnaryHistory unitLeft :=
    unary_cont_closed unary_empty unaryA leftUnitRoute
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryProduct unaryName ledgerRoute
  have unaryScope : UnaryHistory scopeRead :=
    unary_cont_closed unaryLeftUnit unaryLedger scopeRoute
  have sourceScope :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row) scopeRead := by
    exact ⟨hsame_refl scopeRead, unaryScope⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
        (fun row : BHist => Cont unitLeft ledger row ∧ hsame e BHist.Empty)
        (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopeRead sourceScope
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
          ⟨cont_result_hsame_transport scopeRoute (hsame_symm source.left),
            sameUnit⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, scopePkg⟩
    }
  exact ⟨carrierWitness, scopeRoute, scopePkg, cert⟩

end BEDC.Derived.UnaryContMonoidUp
