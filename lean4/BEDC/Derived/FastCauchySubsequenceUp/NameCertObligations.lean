import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.FastCauchySubsequenceUp.TasteGate

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchySubsequenceCarrier [AskSetup] [PackageSetup]
    (S M Q F R W E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory F ∧
    UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem FastCauchySubsequenceNamecertObligations [AskSetup] [PackageSetup]
    {source modulus selector fast regular readback real transport replay provenance localName
      modulusRead selectorRead fastRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory modulus ->
        UnaryHistory selector ->
          UnaryHistory fast ->
            UnaryHistory regular ->
              UnaryHistory readback ->
                UnaryHistory real ->
                  Cont source modulus modulusRead ->
                    Cont modulusRead selector selectorRead ->
                      Cont selectorRead fast fastRead ->
                        Cont fastRead regular regularRead ->
                          Cont regularRead real realRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row realRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row source ∨ hsame row modulus ∨
                                        hsame row selector ∨ hsame row fast ∨
                                          hsame row regular ∨ hsame row readback ∨
                                            hsame row real ∨ hsame row realRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory modulusRead ∧
                                    UnaryHistory selectorRead ∧
                                      UnaryHistory fastRead ∧
                                        UnaryHistory regularRead ∧
                                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro sourceUnary modulusUnary selectorUnary fastUnary regularUnary _readbackUnary
    realUnary modulusRoute selectorRoute fastRoute regularRoute realRoute provenancePkg
    localNamePkg
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary modulusUnary modulusRoute
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusReadUnary selectorUnary selectorRoute
  have fastReadUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorReadUnary fastUnary fastRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed fastReadUnary regularUnary regularRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regularReadUnary realUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row modulus ∨ hsame row selector ∨
              hsame row fast ∨ hsame row regular ∨ hsame row readback ∨
                hsame row real ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
        intro _row _other sameRows sourceSpec
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceSpec.left,
            unary_transport sourceSpec.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceSpec
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceSpec.left))))))
    ledger_sound := by
      intro _row sourceSpec
      exact ⟨sourceSpec.right, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, modulusReadUnary, selectorReadUnary, fastReadUnary, regularReadUnary,
      realReadUnary⟩

theorem FastCauchySubsequenceRegularRoute [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg →
      Cont S M modulusRead →
        Cont modulusRead Q selectorRead →
          Cont selectorRead F fastRead →
            Cont fastRead R regularRead →
              Cont regularRead W sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row F ∨
                          hsame row R ∨ hsame row W ∨ hsame row E ∨
                            hsame row modulusRead ∨ hsame row selectorRead ∨
                              hsame row fastRead ∨ hsame row regularRead ∨
                                hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S M modulusRead ∧
                          Cont modulusRead Q selectorRead ∧
                            Cont selectorRead F fastRead ∧
                              Cont fastRead R regularRead ∧
                                Cont regularRead W sealRead ∧
                                  PkgSig bundle sealRead pkg)
                      hsame ∧ UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                    UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier modulusRoute selectorRoute fastRoute regularRoute sealRoute sealPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryW sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row E ∨ hsame row modulusRead ∨
                hsame row selectorRead ∨ hsame row fastRead ∨ hsame row regularRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M modulusRead ∧
              Cont modulusRead Q selectorRead ∧ Cont selectorRead F fastRead ∧
                Cont fastRead R regularRead ∧ Cont regularRead W sealRead ∧
                  PkgSig bundle sealRead pkg)
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, selectorRoute, fastRoute, regularRoute,
          sealRoute, sealPkg⟩
  }
  exact ⟨cert, modulusUnary, selectorUnary, fastUnary, regularUnary, sealUnary⟩

theorem FastCauchySubsequenceFormalTargetLedger [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead realRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W realRead ->
                Cont realRead E targetRead ->
                  PkgSig bundle targetRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row F ∨
                            hsame row R ∨ hsame row W ∨ hsame row E ∨
                              hsame row targetRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S M modulusRead ∧
                            Cont modulusRead Q selectorRead ∧
                              Cont selectorRead F fastRead ∧
                                Cont fastRead R regularRead ∧
                                  Cont regularRead W realRead ∧
                                    Cont realRead E targetRead ∧
                                      PkgSig bundle targetRead pkg)
                        hsame ∧
                      UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                        UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory realRead ∧ UnaryHistory targetRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusRoute selectorRoute fastRoute regularRoute realRoute targetRoute
    targetPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, provenancePkg, localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary unaryW realRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed realUnary unaryE targetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row E ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M modulusRead ∧ Cont modulusRead Q selectorRead ∧
              Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                Cont regularRead W realRead ∧ Cont realRead E targetRead ∧
                  PkgSig bundle targetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead ⟨hsame_refl targetRead, targetUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, selectorRoute, fastRoute, regularRoute, realRoute,
          targetRoute, targetPkg⟩
  }
  exact
    ⟨cert, modulusUnary, selectorUnary, fastUnary, regularUnary, realUnary, targetUnary,
      provenancePkg, localNamePkg⟩

theorem FastCauchySubsequence_tail_normal_form [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead tailRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg →
      Cont S M modulusRead →
        Cont modulusRead Q selectorRead →
          Cont selectorRead F fastRead →
            Cont fastRead R regularRead →
              Cont regularRead W tailRead →
                PkgSig bundle tailRead pkg →
                  UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                    UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory tailRead ∧ Cont S M modulusRead ∧
                        Cont modulusRead Q selectorRead ∧ Cont selectorRead F fastRead ∧
                          Cont fastRead R regularRead ∧ Cont regularRead W tailRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                              PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont
  intro carrier modulusRoute selectorRoute fastRoute regularRoute tailRoute tailPkg
  obtain ⟨SUnary, MUnary, QUnary, FUnary, RUnary, WUnary, _EUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, provenancePkg, localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed SUnary MUnary modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary QUnary selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary FUnary fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary RUnary regularRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed regularUnary WUnary tailRoute
  exact
    ⟨modulusUnary, selectorUnary, fastUnary, regularUnary, tailUnary,
      modulusRoute, selectorRoute, fastRoute, regularRoute, tailRoute,
      provenancePkg, localNamePkg, tailPkg⟩

theorem FastCauchySubsequenceTailChoiceRefusal [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N selectedRead fastRead regularRead readbackRead
      refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg →
      Cont Q F selectedRead →
        Cont selectedRead R fastRead →
          Cont fastRead W regularRead →
            Cont regularRead E readbackRead →
              Cont H readbackRead refusalRead →
                PkgSig bundle refusalRead pkg →
                  UnaryHistory selectedRead ∧ UnaryHistory fastRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory refusalRead ∧ Cont Q F selectedRead ∧
                        Cont selectedRead R fastRead ∧ Cont fastRead W regularRead ∧
                          Cont regularRead E readbackRead ∧
                            Cont H readbackRead refusalRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont
  intro carrier selectedRoute fastRoute regularRoute readbackRoute refusalRoute refusalPkg
  obtain ⟨_unaryS, _unaryM, unaryQ, unaryF, unaryR, unaryW, unaryE, unaryH,
    _unaryC, unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed unaryQ unaryF selectedRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectedUnary unaryR fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryW regularRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed regularUnary unaryE readbackRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryH readbackUnary refusalRoute
  exact
    ⟨selectedUnary, fastUnary, regularUnary, readbackUnary, refusalUnary,
      selectedRoute, fastRoute, regularRoute, readbackRoute, refusalRoute,
      provenancePkg, refusalPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
