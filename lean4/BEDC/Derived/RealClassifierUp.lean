import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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

inductive RealClassifierUp : Type where
  | packet : RealClassifierUp

def RealClassifierCarrier [AskSetup] [PackageSetup]
    (X Y SX SY RX RY W D C E H K P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory SX ∧ UnaryHistory SY ∧
    UnaryHistory RX ∧ UnaryHistory RY ∧ UnaryHistory W ∧ UnaryHistory D ∧
      UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory K ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle E pkg

theorem RealClassifierRegSeqRatHandoff [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N regRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX regRead ->
        Cont regRead D classifierRead ->
          PkgSig bundle classifierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
                    hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                      hsame row classifierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont SX RX regRead ∧
                    Cont regRead D classifierRead ∧ PkgSig bundle classifierRead pkg)
                hsame ∧
              UnaryHistory regRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier regRoute classifierRoute classifierPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, _syUnary, rxUnary, _ryUnary, _wUnary,
    dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed sxUnary rxUnary regRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed regUnary dUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX regRead ∧ Cont regRead D classifierRead ∧
              PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regRoute, classifierRoute, classifierPkg⟩
  }
  exact ⟨cert, regUnary, classifierUnary⟩

theorem RealClassifierRealSealNonescape [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle E pkg)
          hsame ∧
        UnaryHistory E := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory PkgSig
  intro carrier
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, _wUnary,
    _dUnary, _cUnary, eUnary, _hUnary, _kUnary, _pUnary, _nUnary, sealPkg⟩ :=
    carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle E pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨hsame_refl E, eUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg⟩
  }
  exact ⟨cert, eUnary⟩

theorem RealClassifierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      PkgSig bundle N pkg ->
        SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier namePkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, _wUnary,
    _dUnary, _cUnary, _eUnary, _hUnary, _kUnary, _pUnary, nUnary, _sealPkg⟩ :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg⟩
  }

theorem RealClassifierWindowScope [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N windowRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont W D windowRead ->
        Cont windowRead E classifierRead ->
          PkgSig bundle classifierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
                    hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                      hsame row classifierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W D windowRead ∧
                    Cont windowRead E classifierRead ∧ PkgSig bundle classifierRead pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute classifierRoute classifierPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary eUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧
              Cont windowRead E classifierRead ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, classifierRoute, classifierPkg⟩
  }
  exact ⟨cert, windowUnary, classifierUnary⟩

theorem RealClassifierPublicExactnessSurface [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N windowRead classifierRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont W D windowRead ->
        Cont windowRead E classifierRead ->
          Cont classifierRead N exactRead ->
            PkgSig bundle exactRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                      hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                        hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                          hsame row P ∨ hsame row N ∨ hsame row exactRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W D windowRead ∧
                      Cont windowRead E classifierRead ∧
                        Cont classifierRead N exactRead ∧ PkgSig bundle exactRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory classifierRead ∧
                  UnaryHistory exactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute classifierRoute exactRoute exactPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, eUnary, _hUnary, _kUnary, _pUnary, nUnary, _sealPkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary eUnary classifierRoute
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed classifierUnary nUnary exactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N ∨ hsame row exactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧
              Cont windowRead E classifierRead ∧ Cont classifierRead N exactRead ∧
                PkgSig bundle exactRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exactRead
        ⟨hsame_refl exactRead, exactUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, classifierRoute, exactRoute, exactPkg⟩
  }
  exact ⟨cert, windowUnary, classifierUnary, exactUnary⟩

theorem RealClassifierToleranceWindowDeterminacy [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N X' Y' SX' SY' RX' RY' C' E' H' K' P' N'
      leftReg rightReg leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg →
      RealClassifierCarrier X' Y' SX' SY' RX' RY' W D C' E' H' K' P' N' bundle pkg →
        Cont SX RX leftReg →
          Cont leftReg D leftRead →
            PkgSig bundle leftRead pkg →
              Cont SX' RX' rightReg →
                Cont rightReg D rightRead →
                  PkgSig bundle rightRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          (hsame row leftRead ∨ hsame row rightRead) ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row W ∨ hsame row D ∨ hsame row leftRead ∨
                            hsame row rightRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle leftRead pkg ∧
                            PkgSig bundle rightRead pkg)
                        hsame ∧
                      UnaryHistory leftRead ∧ UnaryHistory rightRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro leftCarrier rightCarrier leftRegRoute leftClassRoute leftPkg
    rightRegRoute rightClassRoute rightPkg
  have leftResult :
      SemanticNameCert
          (fun row : BHist => hsame row leftRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row SY ∨ hsame row RX ∨ hsame row RY ∨
              hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row leftRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX leftReg ∧ Cont leftReg D leftRead ∧
              PkgSig bundle leftRead pkg)
          hsame ∧
        UnaryHistory leftReg ∧ UnaryHistory leftRead :=
    RealClassifierRegSeqRatHandoff leftCarrier leftRegRoute leftClassRoute leftPkg
  have rightResult :
      SemanticNameCert
          (fun row : BHist => hsame row rightRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX' ∨ hsame row SY' ∨ hsame row RX' ∨ hsame row RY' ∨
              hsame row W ∨ hsame row D ∨ hsame row C' ∨ hsame row E' ∨
                hsame row rightRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX' RX' rightReg ∧ Cont rightReg D rightRead ∧
              PkgSig bundle rightRead pkg)
          hsame ∧
        UnaryHistory rightReg ∧ UnaryHistory rightRead :=
    RealClassifierRegSeqRatHandoff rightCarrier rightRegRoute rightClassRoute rightPkg
  have leftUnary : UnaryHistory leftRead := leftResult.right.right
  have rightUnary : UnaryHistory rightRead := rightResult.right.right
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row leftRead ∨ hsame row rightRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row leftRead ∨ hsame row rightRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle leftRead pkg ∧
              PkgSig bundle rightRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro leftRead
        ⟨Or.inl (hsame_refl leftRead), leftUnary⟩
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
        constructor
        · cases source.left with
          | inl leftSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) leftSame)
          | inr rightSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) rightSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl leftSame =>
          exact Or.inr (Or.inr (Or.inl leftSame))
      | inr rightSame =>
          exact Or.inr (Or.inr (Or.inr rightSame))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leftPkg, rightPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary⟩

theorem RealClassifierCommonWindowQuotientRefusal [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N regRead windowRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX regRead ->
        Cont regRead D windowRead ->
          Cont windowRead E publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row regRead ∨
                      hsame row windowRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont SX RX regRead ∧
                      Cont regRead D windowRead ∧ Cont windowRead E publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier regRoute windowRoute publicRoute publicPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, _syUnary, rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed sxUnary rxUnary regRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regUnary dUnary windowRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed windowUnary eUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row regRead ∨
              hsame row windowRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX regRead ∧ Cont regRead D windowRead ∧
              Cont windowRead E publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regRoute, windowRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem RealClassifierSourceScope [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N sourceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont H K sourceRead ->
        Cont sourceRead N publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                    hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                      hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                        hsame row N ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont H K sourceRead ∧
                    Cont sourceRead N publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute publicRoute publicPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, _wUnary,
    _dUnary, _cUnary, _eUnary, hUnary, kUnary, _pUnary, nUnary, _sealPkg⟩ :=
    carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed hUnary kUnary sourceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H K sourceRead ∧ Cont sourceRead N publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, sourceUnary, publicUnary⟩

end BEDC.Derived
